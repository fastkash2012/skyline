#!/usr/bin/env python3
"""
Skyline Kernel  v1.1
====================
Userspace OS layer on top of Linux.

  • Driver system   – pluggable drivers for every hardware/network component
  • Networking      – Wi‑Fi, Bluetooth, routes, ARP, sockets, DNS, ping
  • Permissions     – capabilities + roles + sudo elevation
  • SKL language    – expanded shell language for all frontends
  • Sessions        – env, cwd, jobs, variables

A shell built on Skyline can act as a full interactive environment
while the host Linux continues to run underneath.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import pwd
import re
import signal
import socket
import struct
import subprocess
import sys
import threading
import time
import uuid
from abc import ABC, abstractmethod
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

# ---------------------------------------------------------------------------
# Dependencies
# ---------------------------------------------------------------------------
try:
    import psutil
except ImportError:
    print("FATAL: psutil required → pip install psutil", file=sys.stderr)
    sys.exit(1)

try:
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    from rich import box
    RICH = True
    console = Console()
except ImportError:
    RICH = False
    console = None

try:
    from prompt_toolkit import PromptSession
    from prompt_toolkit.history import FileHistory
    from prompt_toolkit.auto_suggest import AutoSuggestFromHistory
    from prompt_toolkit.completion import WordCompleter
    from prompt_toolkit.styles import Style
    PTK = True
except ImportError:
    PTK = False


# ===========================================================================
# RESULT
# ===========================================================================

@dataclass
class Result:
    ok: bool = True
    data: Any = None
    error: Optional[str] = None
    meta: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict:
        return {"ok": self.ok, "data": self.data, "error": self.error, "meta": self.meta}

    def to_json(self, indent: Optional[int] = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent, default=str)


def _ok(data: Any = None, **meta) -> Result:
    return Result(ok=True, data=data, meta=meta)


def _err(msg: str, **meta) -> Result:
    return Result(ok=False, error=msg, meta=meta)


def _bytes_h(n: int | float) -> str:
    n = float(n)
    for u in ("B", "KB", "MB", "GB", "TB", "PB"):
        if abs(n) < 1024:
            return f"{n:.1f} {u}"
        n /= 1024
    return f"{n:.1f} EB"


def _run(cmd: List[str], timeout: float = 15) -> Tuple[int, str, str]:
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout.strip(), r.stderr.strip()
    except FileNotFoundError:
        return 127, "", f"not found: {cmd[0]}"
    except subprocess.TimeoutExpired:
        return 124, "", "timeout"
    except Exception as e:
        return 1, "", str(e)


def _which(name: str) -> Optional[str]:
    for d in os.environ.get("PATH", "").split(":"):
        p = os.path.join(d, name)
        if os.path.isfile(p) and os.access(p, os.X_OK):
            return p
    return None


# ===========================================================================
# PERMISSIONS
# ===========================================================================

CAP_MONITOR    = "monitor"
CAP_PROC_SELF  = "proc.self"
CAP_PROC_OTHER = "proc.other"
CAP_NET_ADMIN  = "net.admin"
CAP_NET_RAW    = "net.raw"       # ping, bluetooth scan, wifi scan
CAP_SYS_NICE   = "sys.nice"
CAP_SYS_ADMIN  = "sys.admin"
CAP_SESSION    = "session"
CAP_ENV        = "env"
CAP_SCRIPT     = "script"
CAP_DRIVER     = "driver"        # load/unload / driver control
CAP_SUDO       = "sudo"          # may request elevation
CAP_ALL        = "all"

ALL_CAPS = {
    CAP_MONITOR, CAP_PROC_SELF, CAP_PROC_OTHER, CAP_NET_ADMIN, CAP_NET_RAW,
    CAP_SYS_NICE, CAP_SYS_ADMIN, CAP_SESSION, CAP_ENV, CAP_SCRIPT,
    CAP_DRIVER, CAP_SUDO, CAP_ALL,
}

ROLES: Dict[str, Set[str]] = {
    "guest":    {CAP_MONITOR},
    "user":     {CAP_MONITOR, CAP_PROC_SELF, CAP_ENV, CAP_SCRIPT, CAP_NET_RAW, CAP_SUDO},
    "operator": {
        CAP_MONITOR, CAP_PROC_SELF, CAP_PROC_OTHER, CAP_SYS_NICE,
        CAP_ENV, CAP_SCRIPT, CAP_NET_ADMIN, CAP_NET_RAW, CAP_DRIVER, CAP_SUDO,
    },
    "admin":    ALL_CAPS.copy(),
}


@dataclass
class Principal:
    name: str
    role: str = "user"
    caps: Set[str] = field(default_factory=set)
    host_uid: Optional[int] = None
    host_user: Optional[str] = None
    session_id: str = field(default_factory=lambda: uuid.uuid4().hex[:12])
    created: str = field(default_factory=lambda: datetime.now().isoformat(timespec="seconds"))
    # sudo state
    sudo_until: Optional[datetime] = None
    sudo_caps: Set[str] = field(default_factory=set)

    def __post_init__(self):
        if not self.caps:
            self.caps = set(ROLES.get(self.role, ROLES["user"]))
        if CAP_ALL in self.caps:
            self.caps = ALL_CAPS.copy()

    def effective_caps(self) -> Set[str]:
        caps = set(self.caps)
        if self.sudo_until and datetime.now() < self.sudo_until:
            caps |= self.sudo_caps
            if CAP_ALL in caps:
                return ALL_CAPS.copy()
        return caps

    def has(self, *needed: str) -> bool:
        caps = self.effective_caps()
        if CAP_ALL in caps:
            return True
        return any(c in caps for c in needed)

    def require(self, *needed: str) -> Optional[str]:
        if self.has(*needed):
            return None
        return f"permission denied: need one of {needed} (role={self.role}, sudo={'yes' if self.sudo_active() else 'no'})"

    def sudo_active(self) -> bool:
        return bool(self.sudo_until and datetime.now() < self.sudo_until)

    def grant_sudo(self, minutes: float = 5.0, extra: Optional[Set[str]] = None):
        self.sudo_until = datetime.now() + timedelta(minutes=minutes)
        self.sudo_caps = set(extra or ALL_CAPS)

    def drop_sudo(self):
        self.sudo_until = None
        self.sudo_caps = set()


# ===========================================================================
# SESSION
# ===========================================================================

@dataclass
class Job:
    jid: int
    pid: int
    cmd: str
    status: str = "running"
    bg: bool = True


class Session:
    _next_jid = 1

    def __init__(self, principal: Principal):
        self.principal = principal
        self.env: Dict[str, str] = {
            "SKL_USER": principal.name,
            "SKL_ROLE": principal.role,
            "SKL_SESSION": principal.session_id,
            "SKL_HOME": str(Path.home()),
            "SKL_HOST": socket.gethostname(),
            "SKL_VERSION": "1.1.0",
            "PATH": os.environ.get("PATH", ""),
            "PWD": os.getcwd(),
            "TERM": os.environ.get("TERM", "xterm-256color"),
        }
        self.cwd = os.getcwd()
        self.jobs: Dict[int, Job] = {}
        self.vars: Dict[str, str] = {}
        self.last_result: Optional[Result] = None
        self.history: List[str] = []

    def export(self, key: str, value: str):
        self.env[key] = value
        if key == "PWD":
            self.cwd = value

    def getvar(self, name: str) -> Optional[str]:
        return self.vars.get(name) or self.env.get(name) or os.environ.get(name)

    def setvar(self, name: str, value: str):
        self.vars[name] = value

    def add_job(self, pid: int, cmd: str, bg: bool = True) -> int:
        jid = Session._next_jid
        Session._next_jid += 1
        self.jobs[jid] = Job(jid=jid, pid=pid, cmd=cmd, bg=bg)
        return jid

    def refresh_jobs(self):
        for job in self.jobs.values():
            try:
                p = psutil.Process(job.pid)
                st = p.status()
                if st == psutil.STATUS_STOPPED:
                    job.status = "stopped"
                elif st in (psutil.STATUS_ZOMBIE, psutil.STATUS_DEAD):
                    job.status = "done"
                else:
                    job.status = "running"
            except psutil.NoSuchProcess:
                job.status = "done"


# ===========================================================================
# DRIVER SYSTEM  (Skyline 1.1)
# ===========================================================================

class Driver(ABC):
    """Base class for every Skyline component driver."""

    name: str = "base"
    description: str = ""
    version: str = "1.1"
    category: str = "system"   # system | hardware | network | wireless | power | input
    requires_caps: Set[str] = field(default_factory=lambda: {CAP_MONITOR})

    def __init__(self, kernel: "SkylineKernel"):
        self.kernel = kernel
        self.loaded = True
        self.enabled = True
        self._meta: Dict[str, Any] = {}

    @abstractmethod
    def probe(self) -> Result:
        """Detect whether this driver can operate on the host."""
        ...

    @abstractmethod
    def status(self) -> Result:
        """Current operational status / summary."""
        ...

    def info(self) -> Result:
        return _ok({
            "name": self.name,
            "description": self.description,
            "version": self.version,
            "category": self.category,
            "loaded": self.loaded,
            "enabled": self.enabled,
            "requires_caps": sorted(self.requires_caps),
            "meta": self._meta,
        })

    def enable(self) -> Result:
        self.enabled = True
        return _ok({"name": self.name, "enabled": True}, action="enable")

    def disable(self) -> Result:
        self.enabled = False
        return _ok({"name": self.name, "enabled": False}, action="disable")

    def read(self, **kwargs) -> Result:
        """Default read → status. Override for rich data."""
        return self.status()

    def write(self, **kwargs) -> Result:
        return _err(f"Driver '{self.name}' does not support write")

    def ioctl(self, request: str, **kwargs) -> Result:
        """Driver-specific control plane."""
        return _err(f"Unknown ioctl '{request}' for driver '{self.name}'")


class DriverRegistry:
    def __init__(self, kernel: "SkylineKernel"):
        self.kernel = kernel
        self._drivers: Dict[str, Driver] = {}

    def register(self, driver: Driver):
        self._drivers[driver.name] = driver

    def get(self, name: str) -> Optional[Driver]:
        return self._drivers.get(name)

    def list(self) -> List[dict]:
        out = []
        for d in sorted(self._drivers.values(), key=lambda x: (x.category, x.name)):
            probe = d.probe()
            out.append({
                "name": d.name,
                "category": d.category,
                "description": d.description,
                "loaded": d.loaded,
                "enabled": d.enabled,
                "available": probe.ok,
                "probe": probe.data if probe.ok else probe.error,
            })
        return out

    def names(self) -> List[str]:
        return sorted(self._drivers.keys())


# ----- concrete drivers ----------------------------------------------------

class CpuDriver(Driver):
    name = "cpu"
    description = "CPU usage, frequency, per-core, load average"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def __init__(self, kernel):
        super().__init__(kernel)
        self._primed = False

    def _prime(self):
        if not self._primed:
            psutil.cpu_percent(interval=None)
            self._primed = True

    def probe(self) -> Result:
        return _ok({"cores": psutil.cpu_count(), "freq": bool(psutil.cpu_freq())})

    def status(self) -> Result:
        self._prime()
        pct = psutil.cpu_percent(interval=0.15)
        freq = psutil.cpu_freq()
        return _ok({
            "percent": pct,
            "cores_physical": psutil.cpu_count(logical=False) or 0,
            "cores_logical": psutil.cpu_count(logical=True) or 0,
            "freq_mhz": round(freq.current, 1) if freq else None,
            "loadavg": list(os.getloadavg()) if hasattr(os, "getloadavg") else None,
        })

    def read(self, detail: bool = False, **_) -> Result:
        self._prime()
        base = self.status().data
        if detail:
            base["per_core"] = psutil.cpu_percent(interval=0.12, percpu=True)
            times = psutil.cpu_times_percent(interval=0.1)
            base["times"] = {
                "user": times.user, "system": times.system, "idle": times.idle,
                "iowait": getattr(times, "iowait", 0), "irq": getattr(times, "irq", 0),
                "softirq": getattr(times, "softirq", 0),
            }
            try:
                base["stats"] = dict(psutil.cpu_stats()._asdict())
            except Exception:
                pass
        return _ok(base)


class MemDriver(Driver):
    name = "mem"
    description = "RAM and swap memory"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"total": psutil.virtual_memory().total})

    def status(self) -> Result:
        vm = psutil.virtual_memory()
        sm = psutil.swap_memory()
        return _ok({
            "ram": {
                "total": vm.total, "used": vm.used, "available": vm.available,
                "percent": vm.percent,
                "cached": getattr(vm, "cached", 0), "buffers": getattr(vm, "buffers", 0),
                "total_h": _bytes_h(vm.total), "used_h": _bytes_h(vm.used),
                "available_h": _bytes_h(vm.available),
            },
            "swap": {
                "total": sm.total, "used": sm.used, "free": sm.free, "percent": sm.percent,
                "total_h": _bytes_h(sm.total), "used_h": _bytes_h(sm.used),
            },
        })

    def read(self, **_) -> Result:
        return self.status()


class DiskDriver(Driver):
    name = "disk"
    description = "Block devices, partitions, I/O counters"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"partitions": len(psutil.disk_partitions(all=False))})

    def status(self) -> Result:
        return self.read()

    def read(self, path: Optional[str] = None, **_) -> Result:
        parts = []
        for p in psutil.disk_partitions(all=False):
            try:
                u = psutil.disk_usage(p.mountpoint)
            except (PermissionError, OSError):
                continue
            parts.append({
                "device": p.device, "mount": p.mountpoint, "fstype": p.fstype, "opts": p.opts,
                "total": u.total, "used": u.used, "free": u.free, "percent": u.percent,
                "total_h": _bytes_h(u.total), "used_h": _bytes_h(u.used), "free_h": _bytes_h(u.free),
            })
        io = None
        try:
            c = psutil.disk_io_counters()
            if c:
                io = {
                    "read_bytes": c.read_bytes, "write_bytes": c.write_bytes,
                    "read_count": c.read_count, "write_count": c.write_count,
                    "read_h": _bytes_h(c.read_bytes), "write_h": _bytes_h(c.write_bytes),
                }
        except Exception:
            pass
        usage = None
        if path:
            try:
                u = psutil.disk_usage(path)
                usage = {
                    "path": path, "total": u.total, "used": u.used, "free": u.free,
                    "percent": u.percent, "total_h": _bytes_h(u.total),
                    "used_h": _bytes_h(u.used), "free_h": _bytes_h(u.free),
                }
            except Exception as e:
                return _err(str(e))
        return _ok({"partitions": parts, "io": io, "path_usage": usage})


class NetDriver(Driver):
    name = "net"
    description = "Network interfaces, traffic, connections"
    category = "network"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"interfaces": list(psutil.net_if_addrs().keys())})

    def status(self) -> Result:
        return self.read(detail=False)

    def read(self, detail: bool = False, **_) -> Result:
        addrs = psutil.net_if_addrs()
        stats = psutil.net_if_stats()
        io = psutil.net_io_counters(pernic=True)
        ifaces = []
        for name, alist in sorted(addrs.items()):
            st = stats.get(name)
            ips = []
            for a in alist:
                if a.family == socket.AF_INET:
                    ips.append({"family": "inet", "addr": a.address, "netmask": a.netmask,
                                "broadcast": a.broadcast})
                elif a.family == socket.AF_INET6 and not a.address.startswith("fe80"):
                    ips.append({"family": "inet6", "addr": a.address})
                elif getattr(a.family, "name", "") == "AF_LINK" or a.family == 17:
                    ips.append({"family": "mac", "addr": a.address})
            entry: Dict[str, Any] = {
                "name": name, "up": bool(st and st.isup),
                "speed_mbps": st.speed if st else 0, "mtu": st.mtu if st else None,
                "addrs": ips,
            }
            if name in io:
                c = io[name]
                entry.update({
                    "rx": c.bytes_recv, "tx": c.bytes_sent,
                    "rx_h": _bytes_h(c.bytes_recv), "tx_h": _bytes_h(c.bytes_sent),
                    "packets_rx": c.packets_recv, "packets_tx": c.packets_sent,
                    "errin": c.errin, "errout": c.errout,
                    "dropin": c.dropin, "dropout": c.dropout,
                })
            ifaces.append(entry)
        data: Dict[str, Any] = {"interfaces": ifaces}
        if detail:
            conns = []
            for c in psutil.net_connections(kind="inet"):
                conns.append({
                    "fd": c.fd,
                    "type": c.type.name if hasattr(c.type, "name") else str(c.type),
                    "laddr": f"{c.laddr.ip}:{c.laddr.port}" if c.laddr else None,
                    "raddr": f"{c.raddr.ip}:{c.raddr.port}" if c.raddr else None,
                    "status": c.status, "pid": c.pid,
                })
            data["connections"] = conns
            data["connection_count"] = len(conns)
            data["listening"] = [c for c in conns if c["status"] == "LISTEN"]
        return _ok(data)

    def ioctl(self, request: str, **kwargs) -> Result:
        name = kwargs.get("iface") or kwargs.get("name")
        if request == "up":
            if not name:
                return _err("iface required")
            code, out, err = _run(["ip", "link", "set", name, "up"])
            return _ok({"iface": name, "stdout": out}) if code == 0 else _err(err or out)
        if request == "down":
            if not name:
                return _err("iface required")
            code, out, err = _run(["ip", "link", "set", name, "down"])
            return _ok({"iface": name, "stdout": out}) if code == 0 else _err(err or out)
        return _err(f"Unknown net ioctl: {request}")


class SensorsDriver(Driver):
    name = "sensors"
    description = "Temperatures, fans, thermal zones"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        has = False
        try:
            if psutil.sensors_temperatures():
                has = True
        except Exception:
            pass
        if Path("/sys/class/thermal").exists():
            has = True
        return _ok({"available": has}) if has else _err("No sensors")

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        data: Dict[str, Any] = {}
        try:
            temps = psutil.sensors_temperatures()
            if temps:
                data["temps"] = {
                    n: [{"label": e.label, "current": e.current, "high": e.high, "critical": e.critical}
                        for e in ents]
                    for n, ents in temps.items()
                }
        except Exception:
            pass
        try:
            fans = psutil.sensors_fans()
            if fans:
                data["fans"] = {
                    n: [{"label": e.label, "rpm": e.current} for e in ents]
                    for n, ents in fans.items()
                }
        except Exception:
            pass
        zones = []
        base = Path("/sys/class/thermal")
        if base.exists():
            for d in sorted(base.glob("thermal_zone*")):
                try:
                    t = (d / "temp").read_text().strip()
                    typ = (d / "type").read_text().strip() if (d / "type").exists() else d.name
                    zones.append({"zone": d.name, "type": typ, "temp_c": int(t) / 1000.0})
                except Exception:
                    continue
        if zones:
            data["thermal_zones"] = zones
        return _ok(data) if data else _err("No sensor data")


class BatteryDriver(Driver):
    name = "battery"
    description = "Battery / power supply"
    category = "power"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        try:
            b = psutil.sensors_battery()
            return _ok({"present": b is not None})
        except Exception:
            return _err("unsupported")

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        try:
            bat = psutil.sensors_battery()
        except Exception:
            bat = None
        if not bat:
            # sysfs fallback
            ps = Path("/sys/class/power_supply")
            if ps.exists():
                supplies = []
                for d in ps.iterdir():
                    try:
                        t = (d / "type").read_text().strip() if (d / "type").exists() else "?"
                        supplies.append({"name": d.name, "type": t})
                    except Exception:
                        continue
                return _ok({"supplies": supplies}) if supplies else _err("No battery")
            return _err("No battery")
        return _ok({
            "percent": bat.percent, "plugged": bat.power_plugged,
            "secsleft": bat.secsleft if bat.secsleft not in (
                psutil.POWER_TIME_UNLIMITED, psutil.POWER_TIME_UNKNOWN, -1) else None,
        })


class UsbDriver(Driver):
    name = "usb"
    description = "USB devices (sysfs + lsusb)"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"sysfs": Path("/sys/bus/usb/devices").exists()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        devices = []
        usb_base = Path("/sys/bus/usb/devices")
        if usb_base.exists():
            for d in usb_base.iterdir():
                if ":" in d.name:
                    continue
                try:
                    vendor = (d / "idVendor").read_text().strip() if (d / "idVendor").exists() else None
                    product = (d / "idProduct").read_text().strip() if (d / "idProduct").exists() else None
                    manu = (d / "manufacturer").read_text().strip() if (d / "manufacturer").exists() else None
                    prod = (d / "product").read_text().strip() if (d / "product").exists() else None
                    if vendor or product:
                        devices.append({
                            "sysfs": d.name, "vendor_id": vendor, "product_id": product,
                            "manufacturer": manu, "product": prod,
                        })
                except Exception:
                    continue
        if not devices:
            code, out, _ = _run(["lsusb"])
            if code == 0:
                devices = [{"raw": ln} for ln in out.splitlines() if ln]
        return _ok(devices) if devices else _err("No USB info")


class PciDriver(Driver):
    name = "pci"
    description = "PCI devices (lspci)"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"lspci": bool(_which("lspci"))})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        code, out, err = _run(["lspci", "-mm"])
        if code != 0:
            code, out, err = _run(["lspci"])
        if code != 0:
            return _err(err or "lspci failed")
        return _ok([ln for ln in out.splitlines() if ln])


class RoutesDriver(Driver):
    name = "routes"
    description = "IPv4 routing table"
    category = "network"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"proc": Path("/proc/net/route").exists()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        routes = []
        try:
            with open("/proc/net/route") as f:
                next(f)
                for line in f:
                    parts = line.split()
                    if len(parts) < 8:
                        continue
                    iface, dest, gateway, flags, _, _, _, mask = parts[:8]
                    routes.append({
                        "iface": iface,
                        "destination": self._hex_ip(dest),
                        "gateway": self._hex_ip(gateway),
                        "mask": self._hex_ip(mask),
                        "flags": flags,
                    })
        except Exception as e:
            return _err(str(e))
        return _ok(routes)

    @staticmethod
    def _hex_ip(h: str) -> str:
        try:
            return socket.inet_ntoa(struct.pack("<L", int(h, 16)))
        except Exception:
            return h


class ArpDriver(Driver):
    name = "arp"
    description = "ARP neighbour table"
    category = "network"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"proc": Path("/proc/net/arp").exists()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        entries = []
        try:
            with open("/proc/net/arp") as f:
                next(f)
                for line in f:
                    parts = line.split()
                    if len(parts) >= 6:
                        entries.append({
                            "ip": parts[0], "hwtype": parts[1], "flags": parts[2],
                            "mac": parts[3], "mask": parts[4], "device": parts[5],
                        })
        except Exception as e:
            return _err(str(e))
        return _ok(entries)


class DnsDriver(Driver):
    name = "dns"
    description = "Resolver configuration"
    category = "network"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"resolv": Path("/etc/resolv.conf").exists()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        resolv = []
        try:
            with open("/etc/resolv.conf") as f:
                for line in f:
                    line = line.strip()
                    if line.startswith("nameserver"):
                        resolv.append(line.split()[1])
        except Exception:
            pass
        hosts = []
        try:
            with open("/etc/hosts") as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        hosts.append(line)
        except Exception:
            pass
        return _ok({"nameservers": resolv, "hosts_sample": hosts[:20]})


class WifiDriver(Driver):
    """Wi‑Fi via nmcli / iw / iwconfig / sysfs."""
    name = "wifi"
    description = "Wi‑Fi interfaces, scan, connection status"
    category = "wireless"
    requires_caps = {CAP_MONITOR, CAP_NET_RAW}

    def probe(self) -> Result:
        tools = {t: bool(_which(t)) for t in ("nmcli", "iw", "iwconfig", "wpa_cli")}
        wireless = []
        net = Path("/sys/class/net")
        if net.exists():
            for iface in net.iterdir():
                if (iface / "wireless").exists() or (iface / "phy80211").exists():
                    wireless.append(iface.name)
        available = any(tools.values()) or bool(wireless)
        return _ok({"tools": tools, "wireless_ifaces": wireless, "available": available}) \
            if available else _err("No Wi‑Fi support detected")

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        data: Dict[str, Any] = {"interfaces": [], "connections": [], "scan": []}

        # nmcli device
        if _which("nmcli"):
            code, out, _ = _run(["nmcli", "-t", "-f", "DEVICE,TYPE,STATE,CONNECTION", "device"])
            if code == 0:
                for ln in out.splitlines():
                    parts = ln.split(":")
                    if len(parts) >= 4 and parts[1] == "wifi":
                        data["interfaces"].append({
                            "device": parts[0], "type": parts[1],
                            "state": parts[2], "connection": parts[3] or None,
                        })
            code, out, _ = _run(["nmcli", "-t", "-f", "NAME,UUID,TYPE,DEVICE", "connection", "show"])
            if code == 0:
                for ln in out.splitlines():
                    parts = ln.split(":")
                    if len(parts) >= 4 and "wireless" in parts[2]:
                        data["connections"].append({
                            "name": parts[0], "uuid": parts[1],
                            "type": parts[2], "device": parts[3] or None,
                        })

        # iw dev
        if not data["interfaces"] and _which("iw"):
            code, out, _ = _run(["iw", "dev"])
            if code == 0:
                current = None
                for ln in out.splitlines():
                    ln = ln.strip()
                    if ln.startswith("Interface "):
                        current = {"device": ln.split()[1]}
                        data["interfaces"].append(current)
                    elif current and ln.startswith("type "):
                        current["type"] = ln.split()[1]
                    elif current and ln.startswith("ssid "):
                        current["ssid"] = ln[5:]

        # sysfs fallback
        if not data["interfaces"]:
            net = Path("/sys/class/net")
            if net.exists():
                for iface in net.iterdir():
                    if (iface / "wireless").exists() or (iface / "phy80211").exists():
                        data["interfaces"].append({"device": iface.name, "source": "sysfs"})

        return _ok(data)

    def ioctl(self, request: str, **kwargs) -> Result:
        if request == "scan":
            return self._scan(kwargs.get("iface"))
        if request == "connect":
            ssid = kwargs.get("ssid")
            password = kwargs.get("password")
            if not ssid:
                return _err("ssid required")
            return self._connect(ssid, password, kwargs.get("iface"))
        if request == "disconnect":
            return self._disconnect(kwargs.get("iface"))
        if request == "radio":
            state = kwargs.get("state", "on")
            return self._radio(state)
        return _err(f"Unknown wifi ioctl: {request}")

    def _scan(self, iface: Optional[str] = None) -> Result:
        if _which("nmcli"):
            code, out, err = _run(["nmcli", "-t", "-f", "SSID,SIGNAL,SECURITY,CHAN,BARS", "device", "wifi", "list"], timeout=30)
            if code == 0:
                aps = []
                for ln in out.splitlines():
                    parts = ln.split(":")
                    if len(parts) >= 3:
                        aps.append({
                            "ssid": parts[0], "signal": parts[1],
                            "security": parts[2], "channel": parts[3] if len(parts) > 3 else None,
                        })
                return _ok(aps)
            return _err(err or "nmcli scan failed")
        if _which("iw") and iface:
            code, out, err = _run(["iw", "dev", iface, "scan"], timeout=30)
            if code == 0:
                return _ok({"raw": out[:5000]})
            return _err(err or "iw scan failed")
        return _err("No Wi‑Fi scan tool available (need nmcli or iw)")

    def _connect(self, ssid: str, password: Optional[str], iface: Optional[str]) -> Result:
        if not _which("nmcli"):
            return _err("nmcli required for connect")
        cmd = ["nmcli", "device", "wifi", "connect", ssid]
        if password:
            cmd += ["password", password]
        if iface:
            cmd += ["ifname", iface]
        code, out, err = _run(cmd, timeout=45)
        return _ok({"ssid": ssid, "stdout": out}) if code == 0 else _err(err or out)

    def _disconnect(self, iface: Optional[str]) -> Result:
        if not _which("nmcli"):
            return _err("nmcli required")
        target = iface or "wifi"
        code, out, err = _run(["nmcli", "device", "disconnect", target])
        return _ok({"stdout": out}) if code == 0 else _err(err or out)

    def _radio(self, state: str) -> Result:
        if _which("nmcli"):
            code, out, err = _run(["nmcli", "radio", "wifi", state])
            return _ok({"radio": state, "stdout": out}) if code == 0 else _err(err or out)
        if _which("rfkill"):
            action = "unblock" if state in ("on", "enable") else "block"
            code, out, err = _run(["rfkill", action, "wifi"])
            return _ok({"radio": state}) if code == 0 else _err(err or out)
        return _err("No radio control tool")


class BluetoothDriver(Driver):
    """Bluetooth via bluetoothctl / hciconfig / sysfs."""
    name = "bluetooth"
    description = "Bluetooth adapters, devices, scan"
    category = "wireless"
    requires_caps = {CAP_MONITOR, CAP_NET_RAW}

    def probe(self) -> Result:
        tools = {t: bool(_which(t)) for t in ("bluetoothctl", "hciconfig", "btmgmt")}
        sysfs = Path("/sys/class/bluetooth").exists()
        available = any(tools.values()) or sysfs
        return _ok({"tools": tools, "sysfs": sysfs, "available": available}) \
            if available else _err("No Bluetooth support detected")

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        data: Dict[str, Any] = {"adapters": [], "devices": []}

        if _which("bluetoothctl"):
            code, out, _ = _run(["bluetoothctl", "list"])
            if code == 0:
                for ln in out.splitlines():
                    # Controller XX:XX:XX:XX:XX:XX Name
                    parts = ln.split()
                    if len(parts) >= 2 and parts[0] == "Controller":
                        data["adapters"].append({
                            "mac": parts[1],
                            "name": " ".join(parts[2:]) if len(parts) > 2 else None,
                        })
            code, out, _ = _run(["bluetoothctl", "devices"])
            if code == 0:
                for ln in out.splitlines():
                    parts = ln.split()
                    if len(parts) >= 2 and parts[0] == "Device":
                        data["devices"].append({
                            "mac": parts[1],
                            "name": " ".join(parts[2:]) if len(parts) > 2 else None,
                        })

        if not data["adapters"] and _which("hciconfig"):
            code, out, _ = _run(["hciconfig"])
            if code == 0:
                data["adapters_raw"] = out

        if not data["adapters"]:
            bt = Path("/sys/class/bluetooth")
            if bt.exists():
                for d in bt.iterdir():
                    data["adapters"].append({"sysfs": d.name})

        return _ok(data)

    def ioctl(self, request: str, **kwargs) -> Result:
        if request == "scan":
            return self._scan(kwargs.get("timeout", 8))
        if request == "power":
            return self._power(kwargs.get("state", "on"))
        if request == "pair":
            mac = kwargs.get("mac")
            if not mac:
                return _err("mac required")
            return self._pair(mac)
        if request == "connect":
            mac = kwargs.get("mac")
            if not mac:
                return _err("mac required")
            return self._connect(mac)
        if request == "disconnect":
            mac = kwargs.get("mac")
            if not mac:
                return _err("mac required")
            return self._disconnect(mac)
        return _err(f"Unknown bluetooth ioctl: {request}")

    def _scan(self, timeout: float = 8) -> Result:
        if not _which("bluetoothctl"):
            return _err("bluetoothctl required for scan")
        # non-interactive scan
        code, out, err = _run(
            ["bluetoothctl", "--timeout", str(int(timeout)), "scan", "on"],
            timeout=timeout + 5,
        )
        # list discovered
        code2, out2, _ = _run(["bluetoothctl", "devices"])
        devices = []
        if code2 == 0:
            for ln in out2.splitlines():
                parts = ln.split()
                if len(parts) >= 2 and parts[0] == "Device":
                    devices.append({"mac": parts[1], "name": " ".join(parts[2:]) if len(parts) > 2 else None})
        return _ok({"devices": devices, "scan_output": out[:2000]})

    def _power(self, state: str) -> Result:
        if _which("bluetoothctl"):
            onoff = "on" if state in ("on", "enable", "1") else "off"
            code, out, err = _run(["bluetoothctl", "power", onoff])
            return _ok({"power": onoff, "stdout": out}) if code == 0 else _err(err or out)
        if _which("rfkill"):
            action = "unblock" if state in ("on", "enable", "1") else "block"
            code, out, err = _run(["rfkill", action, "bluetooth"])
            return _ok({"power": state}) if code == 0 else _err(err or out)
        return _err("No Bluetooth power control")

    def _pair(self, mac: str) -> Result:
        if not _which("bluetoothctl"):
            return _err("bluetoothctl required")
        code, out, err = _run(["bluetoothctl", "pair", mac], timeout=30)
        return _ok({"mac": mac, "stdout": out}) if code == 0 else _err(err or out)

    def _connect(self, mac: str) -> Result:
        if not _which("bluetoothctl"):
            return _err("bluetoothctl required")
        code, out, err = _run(["bluetoothctl", "connect", mac], timeout=20)
        return _ok({"mac": mac, "stdout": out}) if code == 0 else _err(err or out)

    def _disconnect(self, mac: str) -> Result:
        if not _which("bluetoothctl"):
            return _err("bluetoothctl required")
        code, out, err = _run(["bluetoothctl", "disconnect", mac])
        return _ok({"mac": mac, "stdout": out}) if code == 0 else _err(err or out)


class ProcessDriver(Driver):
    name = "proc"
    description = "Process list and control"
    category = "system"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"count": len(psutil.pids())})

    def status(self) -> Result:
        return self.read(limit=10)

    def read(self, sort: str = "cpu", limit: int = 20,
             user: Optional[str] = None, name: Optional[str] = None, pid: Optional[int] = None, **_) -> Result:
        if pid is not None:
            return self._one(pid)
        # list
        psutil.cpu_percent(interval=None)
        raw = []
        for p in psutil.process_iter(["pid", "name", "username", "status", "ppid", "cmdline"]):
            try:
                info = p.info
                info["cpu"] = p.cpu_percent(interval=0)
                info["mem"] = p.memory_percent()
                raw.append(info)
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                continue
        time.sleep(0.15)
        for p in psutil.process_iter(["pid"]):
            try:
                for info in raw:
                    if info["pid"] == p.pid:
                        info["cpu"] = p.cpu_percent(interval=0)
                        break
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                pass
        if user:
            raw = [x for x in raw if (x.get("username") or "") == user]
        if name:
            nf = name.lower()
            raw = [x for x in raw if nf in (x.get("name") or "").lower()]
        key = "mem" if sort in ("mem", "memory") else "cpu"
        raw.sort(key=lambda x: x.get(key) or 0, reverse=True)
        out = []
        for info in raw[:limit]:
            out.append({
                "pid": info["pid"], "ppid": info.get("ppid"),
                "name": info.get("name"), "user": info.get("username"),
                "cpu": round(info.get("cpu") or 0, 1),
                "mem": round(info.get("mem") or 0, 1),
                "status": info.get("status"),
                "cmdline": " ".join(info.get("cmdline") or [])[:100],
            })
        return _ok(out, total=len(raw), sort=key, limit=limit)

    def _one(self, pid: int) -> Result:
        try:
            p = psutil.Process(pid)
            with p.oneshot():
                mi = p.memory_info()
                return _ok({
                    "pid": p.pid, "ppid": p.ppid(), "name": p.name(),
                    "exe": p.exe() if hasattr(p, "exe") else None,
                    "cmdline": p.cmdline(), "user": p.username(),
                    "status": p.status(),
                    "cpu": p.cpu_percent(interval=0.1),
                    "mem": p.memory_percent(),
                    "mem_rss": mi.rss, "mem_rss_h": _bytes_h(mi.rss),
                    "threads": p.num_threads(), "nice": p.nice(),
                    "create_time": datetime.fromtimestamp(p.create_time()).isoformat(timespec="seconds"),
                    "cwd": p.cwd() if hasattr(p, "cwd") else None,
                })
        except psutil.NoSuchProcess:
            return _err(f"No process PID {pid}")
        except psutil.AccessDenied:
            return _err(f"Access denied for PID {pid}")


class SystemDriver(Driver):
    name = "system"
    description = "Host OS and Skyline identity"
    category = "system"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"platform": platform.system()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        uname = platform.uname()
        boot = datetime.fromtimestamp(psutil.boot_time())
        uptime = datetime.now() - boot
        skyl_uptime = datetime.now() - self.kernel.boot_time
        return _ok({
            "hostname": socket.gethostname(),
            "os": f"{uname.system} {uname.release}",
            "kernel_host": uname.version,
            "arch": uname.machine,
            "processor": uname.processor or platform.processor() or "N/A",
            "python": platform.python_version(),
            "host_boot": boot.isoformat(timespec="seconds"),
            "host_uptime": str(uptime).split(".")[0],
            "skyline_version": self.kernel.VERSION,
            "skyline_uptime": str(skyl_uptime).split(".")[0],
            "skyline_sessions": len(self.kernel.sessions),
        })


# ===========================================================================
# KERNEL
# ===========================================================================

class SkylineKernel:
    VERSION = "1.1.0"
    NAME = "Skyline"

    def __init__(self):
        self.boot_time = datetime.now()
        self.sessions: Dict[str, Session] = {}
        self.drivers = DriverRegistry(self)
        self._register_builtin_drivers()
        self._default_principal = self._make_principal_from_host()

    def _register_builtin_drivers(self):
        for cls in (
            SystemDriver, CpuDriver, MemDriver, DiskDriver, NetDriver,
            SensorsDriver, BatteryDriver, UsbDriver, PciDriver,
            RoutesDriver, ArpDriver, DnsDriver,
            WifiDriver, BluetoothDriver, ProcessDriver,
        ):
            self.drivers.register(cls(self))

    def _make_principal_from_host(self, role: str = "user") -> Principal:
        try:
            host_user = pwd.getpwuid(os.getuid()).pw_name
            host_uid = os.getuid()
        except Exception:
            host_user, host_uid = "skyline", getattr(os, "getuid", lambda: 0)()
        if host_uid == 0:
            role = "admin"
        return Principal(name=host_user, role=role, host_uid=host_uid, host_user=host_user)

    def new_session(self, name: Optional[str] = None, role: str = "user") -> Session:
        p = self._make_principal_from_host(role=role)
        if name:
            p.name = name
        sess = Session(p)
        self.sessions[p.session_id] = sess
        return sess

    # convenience passthroughs used by older call sites / snapshot
    def snapshot(self) -> Result:
        cpu = self.drivers.get("cpu")
        mem = self.drivers.get("mem")
        disk = self.drivers.get("disk")
        net = self.drivers.get("net")
        c = cpu.read().data if cpu else {}
        m = mem.read().data if mem else {}
        d = disk.read().data if disk else {}
        n = net.read().data if net else {}
        return _ok({
            "ts": datetime.now().isoformat(timespec="seconds"),
            "cpu_percent": c.get("percent"),
            "mem_percent": (m.get("ram") or {}).get("percent"),
            "disk_root_percent": next(
                (p["percent"] for p in (d.get("partitions") or []) if p["mount"] == "/"), None),
            "loadavg": c.get("loadavg"),
            "net_rx": sum(i.get("rx", 0) for i in (n.get("interfaces") or [])),
            "net_tx": sum(i.get("tx", 0) for i in (n.get("interfaces") or [])),
            "skyline": self.VERSION,
            "drivers": len(self.drivers.names()),
        })

    def kill(self, pid: int, sig: str, sess: Session) -> Result:
        deny = sess.principal.require(CAP_PROC_OTHER, CAP_PROC_SELF, CAP_SYS_ADMIN)
        if deny:
            if sess.principal.has(CAP_PROC_SELF):
                try:
                    if psutil.Process(pid).uids().real != os.getuid():
                        return _err(deny)
                except Exception:
                    return _err(deny)
            else:
                return _err(deny)
        sig_map = {
            "TERM": signal.SIGTERM, "KILL": signal.SIGKILL,
            "STOP": signal.SIGSTOP, "CONT": signal.SIGCONT,
            "HUP": signal.SIGHUP, "INT": signal.SIGINT,
            "QUIT": signal.SIGQUIT, "USR1": signal.SIGUSR1, "USR2": signal.SIGUSR2,
        }
        s = sig_map.get(sig.upper())
        if s is None:
            try:
                s = int(sig)
            except ValueError:
                return _err(f"Unknown signal: {sig}")
        try:
            p = psutil.Process(pid)
            name = p.name()
            p.send_signal(s)
            return _ok({"pid": pid, "name": name, "signal": sig.upper()}, action="kill")
        except psutil.NoSuchProcess:
            return _err(f"No process PID {pid}")
        except psutil.AccessDenied:
            return _err(f"Host permission denied for PID {pid}")
        except Exception as e:
            return _err(str(e))

    def renice(self, pid: int, nice: int, sess: Session) -> Result:
        deny = sess.principal.require(CAP_SYS_NICE, CAP_SYS_ADMIN)
        if deny:
            return _err(deny)
        if not -20 <= nice <= 19:
            return _err("nice must be -20..19")
        try:
            p = psutil.Process(pid)
            old = p.nice()
            p.nice(nice)
            return _ok({"pid": pid, "old_nice": old, "new_nice": nice}, action="renice")
        except Exception as e:
            return _err(str(e))

    def set_affinity(self, pid: int, cpus: List[int], sess: Session) -> Result:
        deny = sess.principal.require(CAP_SYS_NICE, CAP_SYS_ADMIN)
        if deny:
            return _err(deny)
        try:
            p = psutil.Process(pid)
            old = p.cpu_affinity()
            p.cpu_affinity(cpus)
            return _ok({"pid": pid, "old": old, "new": cpus}, action="affinity")
        except Exception as e:
            return _err(str(e))

    def net_ping(self, host: str, count: int = 3, timeout: float = 2.0) -> Result:
        code, out, err = _run(
            ["ping", "-c", str(count), "-W", str(int(timeout)), host],
            timeout=timeout * count + 5,
        )
        return _ok({"host": host, "exit": code, "stdout": out, "ok": code == 0})

    def net_resolve(self, host: str) -> Result:
        try:
            infos = socket.getaddrinfo(host, None)
            addrs = sorted({i[4][0] for i in infos})
            return _ok({"host": host, "addresses": addrs})
        except Exception as e:
            return _err(str(e))


# ===========================================================================
# SKL LANGUAGE
# ===========================================================================

@dataclass
class Statement:
    verb: str
    obj: Optional[str] = None
    args: List[str] = field(default_factory=list)
    flags: Dict[str, str] = field(default_factory=dict)
    raw: str = ""
    background: bool = False
    sudo: bool = False


class SKLParser:
    VERBS = {
        "get", "list", "show", "info", "snapshot",
        "kill", "terminate", "forcekill", "suspend", "resume",
        "renice", "affinity",
        "ifup", "ifdown", "ping", "resolve", "routes", "arp", "sockets", "dns",
        "hardware", "usb", "pci", "sensors", "thermal",
        "cd", "pwd", "env", "set", "export", "unset",
        "whoami", "id", "caps", "role", "sessions", "jobs",
        "exec", "run", "system",
        "help", "version", "clear", "history",
        "watch", "login", "su", "echo", "cat", "ls",
        # 1.1
        "drivers", "driver", "wifi", "bluetooth", "bt",
        "sudo", "unsudo",
    }

    ALIASES = {
        "ps": "list", "top": "list",
        "stop": "suspend", "cont": "resume", "continue": "resume",
        "term": "terminate", "sigkill": "forcekill",
        "?": "help", "man": "help", "snap": "snapshot", "ver": "version",
        "bt": "bluetooth",
    }

    OBJECTS = {
        "cpu", "mem", "memory", "disk", "net", "network", "proc", "process",
        "system", "sys", "sensors", "temp", "battery", "bat", "power",
        "hardware", "hw", "usb", "pci", "routes", "arp", "sockets", "dns",
        "thermal", "iface", "interface", "wifi", "bluetooth", "bt",
    }

    def parse_line(self, line: str) -> Optional[Statement]:
        line = line.strip()
        if not line or line.startswith("#"):
            return None
        if "#" in line:
            line = re.sub(r"\s+#.*$", "", line)

        background = False
        if line.endswith("&"):
            background = True
            line = line[:-1].rstrip()

        tokens = self._tokenize(line)
        if not tokens:
            return None

        sudo = False
        if tokens[0].lower() == "sudo":
            sudo = True
            tokens = tokens[1:]
            if not tokens:
                return Statement(verb="sudo", raw=line, sudo=True)
            # bare sudo with only flags:  sudo for=5
            if all(("=" in t and not t.startswith("=")) or t.startswith("-") for t in tokens):
                flags_only: Dict[str, str] = {}
                for t in tokens:
                    if "=" in t and not t.startswith("="):
                        k, _, v = t.partition("=")
                        flags_only[k.lower().lstrip("-")] = v
                    elif t.startswith("--"):
                        flags_only[t[2:].lower()] = "1"
                    elif t.startswith("-") and len(t) > 1:
                        flags_only[t.lstrip("-").lower()] = "1"
                return Statement(verb="sudo", flags=flags_only, raw=line, sudo=True)

        verb = tokens[0].lower()
        verb = self.ALIASES.get(verb, verb)

        obj = None
        args: List[str] = []
        flags: Dict[str, str] = {}
        rest = tokens[1:]

        if rest and "=" not in rest[0] and not rest[0].startswith("-"):
            if rest[0].lower() in self.OBJECTS or verb in ("get", "list", "show", "info", "driver"):
                obj = rest[0].lower()
                obj = {
                    "memory": "mem", "network": "net", "process": "proc",
                    "sys": "system", "temp": "sensors", "bat": "battery",
                    "power": "battery", "iface": "net", "interface": "net",
                    "hw": "hardware", "bt": "bluetooth",
                }.get(obj, obj)
                rest = rest[1:]

        for t in rest:
            if "=" in t and not t.startswith("="):
                k, _, v = t.partition("=")
                flags[k.lower().lstrip("-")] = v
            elif t.startswith("--"):
                flags[t[2:].lower()] = "1"
            elif t.startswith("-") and len(t) > 1 and not t[1].isdigit():
                flags[t.lstrip("-").lower()] = "1"
            else:
                args.append(t)

        return Statement(verb=verb, obj=obj, args=args, flags=flags, raw=line,
                         background=background, sudo=sudo)

    def parse(self, text: str) -> List[Statement]:
        text = text.replace("&&", ";")
        stmts = []
        for part in re.split(r"[;\n]", text):
            s = self.parse_line(part)
            if s:
                stmts.append(s)
        return stmts

    def _tokenize(self, line: str) -> List[str]:
        tokens = []
        current: List[str] = []
        in_quote = False
        quote_char = None
        for ch in line:
            if in_quote:
                if ch == quote_char:
                    in_quote = False
                else:
                    current.append(ch)
            else:
                if ch in ('"', "'"):
                    in_quote = True
                    quote_char = ch
                elif ch.isspace():
                    if current:
                        tokens.append("".join(current))
                        current = []
                else:
                    current.append(ch)
        if current:
            tokens.append("".join(current))
        return tokens


class SKLExecutor:
    def __init__(self, kernel: SkylineKernel, session: Session):
        self.kernel = kernel
        self.session = session
        self.parser = SKLParser()

    def run(self, text: str) -> List[Result]:
        text = self._expand(text)
        results = []
        for stmt in self.parser.parse(text):
            # sudo prefix: temporarily elevate for this statement
            elevated = False
            if stmt.sudo or stmt.verb == "sudo":
                r = self._handle_sudo(stmt)
                if stmt.verb == "sudo" and not stmt.args and not stmt.obj:
                    results.append(r)
                    continue
                if not r.ok:
                    results.append(r)
                    continue
                elevated = True

            r = self.execute(stmt)
            self.session.last_result = r
            results.append(r)

            if elevated and stmt.flags.get("keep") != "1":
                # one-shot sudo unless keep=1
                pass  # grant_sudo already set a timer; leave it
        return results

    def _expand(self, text: str) -> str:
        def repl(m):
            name = m.group(1) or m.group(2)
            return self.session.getvar(name) or ""
        return re.sub(r"\$\{([A-Za-z_][A-Za-z0-9_]*)\}|\$([A-Za-z_][A-Za-z0-9_]*)", repl, text)

    def _handle_sudo(self, stmt: Statement) -> Result:
        p = self.session.principal
        deny = p.require(CAP_SUDO, CAP_SYS_ADMIN, CAP_ALL)
        if deny and os.getuid() != 0:
            return _err(deny)
        minutes = float(stmt.flags.get("for", stmt.flags.get("minutes", "5")))
        p.grant_sudo(minutes=minutes)
        return _ok({
            "sudo": True,
            "until": p.sudo_until.isoformat(timespec="seconds") if p.sudo_until else None,
            "minutes": minutes,
            "role": p.role,
            "effective_caps": sorted(p.effective_caps()),
        }, action="sudo")

    def execute(self, stmt: Statement) -> Result:
        v, o, a, f = stmt.verb, stmt.obj, stmt.args, stmt.flags
        sess = self.session
        k = self.kernel

        try:
            # ---- sudo / unsudo -------------------------------------------
            if v == "sudo":
                return self._handle_sudo(stmt)
            if v == "unsudo":
                sess.principal.drop_sudo()
                return _ok({"sudo": False}, action="unsudo")

            # ---- drivers -------------------------------------------------
            if v == "drivers":
                return _ok(k.drivers.list())
            if v == "driver":
                return self._driver_cmd(o, a, f)

            # ---- wifi / bluetooth high-level -----------------------------
            if v == "wifi":
                return self._wifi_cmd(o, a, f)
            if v in ("bluetooth", "bt"):
                return self._bt_cmd(o, a, f)

            # ---- meta / session ------------------------------------------
            if v == "help":
                return self._help(o or (a[0] if a else None))
            if v == "version":
                return _ok({
                    "name": SkylineKernel.NAME, "version": SkylineKernel.VERSION,
                    "host": platform.platform(), "python": platform.python_version(),
                    "drivers": k.drivers.names(),
                })
            if v in ("whoami", "id"):
                p = sess.principal
                return _ok({
                    "user": p.name, "role": p.role, "session": p.session_id,
                    "host_user": p.host_user,
                    "caps": sorted(p.effective_caps()),
                    "sudo": p.sudo_active(),
                    "sudo_until": p.sudo_until.isoformat(timespec="seconds") if p.sudo_until else None,
                })
            if v == "caps":
                return _ok({
                    "role": sess.principal.role,
                    "capabilities": sorted(sess.principal.effective_caps()),
                    "sudo": sess.principal.sudo_active(),
                })
            if v == "role":
                if a:
                    deny = sess.principal.require(CAP_SESSION, CAP_SYS_ADMIN)
                    if deny:
                        return _err(deny)
                    new_role = a[0]
                    if new_role not in ROLES:
                        return _err(f"Unknown role: {new_role}")
                    sess.principal.role = new_role
                    sess.principal.caps = set(ROLES[new_role])
                    if CAP_ALL in sess.principal.caps:
                        sess.principal.caps = ALL_CAPS.copy()
                    sess.env["SKL_ROLE"] = new_role
                    return _ok({"role": new_role, "caps": sorted(sess.principal.caps)})
                return _ok({"role": sess.principal.role})
            if v == "sessions":
                deny = sess.principal.require(CAP_SESSION, CAP_SYS_ADMIN)
                if deny:
                    return _err(deny)
                return _ok([
                    {"id": s.principal.session_id, "user": s.principal.name,
                     "role": s.principal.role, "cwd": s.cwd}
                    for s in k.sessions.values()
                ])
            if v == "jobs":
                sess.refresh_jobs()
                return _ok([asdict(j) for j in sess.jobs.values()])

            # ---- environment ---------------------------------------------
            if v == "pwd":
                return _ok(sess.cwd)
            if v == "cd":
                target = a[0] if a else sess.env.get("SKL_HOME", str(Path.home()))
                target = os.path.expanduser(target)
                if not os.path.isabs(target):
                    target = os.path.join(sess.cwd, target)
                target = os.path.normpath(target)
                if not os.path.isdir(target):
                    return _err(f"Not a directory: {target}")
                try:
                    os.chdir(target)
                    sess.cwd = target
                    sess.export("PWD", target)
                    return _ok(target)
                except Exception as e:
                    return _err(str(e))
            if v == "env":
                if a:
                    return _ok({a[0]: sess.getvar(a[0])})
                return _ok(dict(sess.env))
            if v in ("set", "export"):
                deny = sess.principal.require(CAP_ENV)
                if deny:
                    return _err(deny)
                if len(a) >= 2:
                    key, val = a[0], a[1]
                elif len(a) == 1 and "=" in a[0]:
                    key, _, val = a[0].partition("=")
                else:
                    return _err("set/export NAME VALUE")
                sess.setvar(key, val)
                if v == "export":
                    sess.export(key, val)
                return _ok({key: val})
            if v == "unset":
                if not a:
                    return _err("unset NAME")
                sess.vars.pop(a[0], None)
                sess.env.pop(a[0], None)
                return _ok({"unset": a[0]})
            if v == "echo":
                return _ok(" ".join(a))
            if v == "history":
                return _ok(sess.history[-50:])
            if v == "ls":
                path = a[0] if a else sess.cwd
                path = os.path.expanduser(path)
                if not os.path.isabs(path):
                    path = os.path.join(sess.cwd, path)
                try:
                    return _ok(sorted(os.listdir(path)), path=path)
                except Exception as e:
                    return _err(str(e))
            if v == "cat":
                if not a:
                    return _err("cat FILE")
                path = a[0] if os.path.isabs(a[0]) else os.path.join(sess.cwd, a[0])
                try:
                    with open(path, "r", errors="replace") as fh:
                        return _ok(fh.read()[:100_000])
                except Exception as e:
                    return _err(str(e))

            # ---- monitor via drivers -------------------------------------
            if v in ("get", "list", "show", "info"):
                return self._get(o, a, f)
            if v == "snapshot":
                return k.snapshot()
            if v in ("hardware", "usb", "pci", "sensors", "thermal", "routes", "arp", "dns"):
                # map short verbs to drivers
                name = {"hardware": "system", "thermal": "sensors"}.get(v, v)
                drv = k.drivers.get(name)
                if not drv:
                    return _err(f"No driver: {name}")
                return drv.read()

            if v == "ping":
                if not a:
                    return _err("ping HOST [count=3]")
                deny = sess.principal.require(CAP_NET_RAW, CAP_MONITOR)
                if deny:
                    return _err(deny)
                return k.net_ping(a[0], count=int(f.get("count", f.get("c", "3"))))
            if v == "resolve":
                if not a:
                    return _err("resolve HOST")
                return k.net_resolve(a[0])
            if v == "sockets":
                try:
                    conns = psutil.net_connections(kind=f.get("kind", "inet"))
                    out = [{
                        "fd": c.fd, "status": c.status, "pid": c.pid,
                        "laddr": f"{c.laddr.ip}:{c.laddr.port}" if c.laddr else None,
                        "raddr": f"{c.raddr.ip}:{c.raddr.port}" if c.raddr else None,
                    } for c in conns]
                    return _ok(out, count=len(out))
                except Exception as e:
                    return _err(str(e))

            # ---- process control -----------------------------------------
            if v == "kill":
                if not a:
                    return _err("kill PID [signal=TERM]")
                sig = f.get("signal") or f.get("sig") or (a[1] if len(a) > 1 else "TERM")
                return k.kill(int(a[0]), sig, sess)
            if v == "terminate":
                return k.kill(int(a[0]), "TERM", sess) if a else _err("PID required")
            if v == "forcekill":
                return k.kill(int(a[0]), "KILL", sess) if a else _err("PID required")
            if v == "suspend":
                return k.kill(int(a[0]), "STOP", sess) if a else _err("PID required")
            if v == "resume":
                return k.kill(int(a[0]), "CONT", sess) if a else _err("PID required")
            if v == "renice":
                if len(a) < 2:
                    return _err("renice PID NICE")
                return k.renice(int(a[0]), int(a[1]), sess)
            if v == "affinity":
                if len(a) < 2:
                    return _err("affinity PID cpu0,cpu1,...")
                return k.set_affinity(int(a[0]), [int(x) for x in a[1].split(",")], sess)

            # ---- net control ---------------------------------------------
            if v in ("ifup", "ifdown"):
                deny = sess.principal.require(CAP_NET_ADMIN, CAP_SYS_ADMIN)
                if deny:
                    return _err(deny)
                name = o or (a[0] if a else None)
                if not name:
                    return _err(f"{v} IFACE")
                drv = k.drivers.get("net")
                return drv.ioctl("up" if v == "ifup" else "down", iface=name)

            # ---- host escape ---------------------------------------------
            if v in ("exec", "run", "system"):
                deny = sess.principal.require(CAP_SYS_ADMIN, CAP_SCRIPT)
                if deny:
                    return _err(deny)
                if not a:
                    return _err("exec COMMAND...")
                cmd = a if v == "exec" else ["bash", "-c", " ".join(a)]
                try:
                    r = subprocess.run(cmd, capture_output=True, text=True, timeout=60, cwd=sess.cwd)
                    return _ok({"exit": r.returncode, "stdout": r.stdout, "stderr": r.stderr}, action="exec")
                except Exception as e:
                    return _err(str(e))

            if v == "watch":
                return _ok({
                    "_watch": True,
                    "targets": o or "cpu,mem",
                    "interval": float(f.get("interval", f.get("i", "1"))),
                }, frontend="watch")

            if v in ("login", "su"):
                role = a[0] if a else "user"
                if role not in ROLES:
                    return _err(f"Unknown role: {role}")
                if role in ("admin", "operator") and not sess.principal.has(CAP_SESSION, CAP_SYS_ADMIN, CAP_ALL):
                    if os.getuid() != 0:
                        return _err("Cannot elevate without session/admin capability or host root")
                sess.principal.role = role
                sess.principal.caps = set(ROLES[role])
                if CAP_ALL in sess.principal.caps:
                    sess.principal.caps = ALL_CAPS.copy()
                sess.env["SKL_ROLE"] = role
                return _ok({"user": sess.principal.name, "role": role, "caps": sorted(sess.principal.caps)})

            return _err(f"Unknown verb: {v}. Try 'help'")

        except ValueError as e:
            return _err(f"Invalid argument: {e}")
        except Exception as e:
            return _err(str(e))

    # ----- driver / wifi / bt helpers -------------------------------------

    def _driver_cmd(self, obj: Optional[str], args: List[str], flags: Dict[str, str]) -> Result:
        k = self.kernel
        if not obj and not args:
            return _ok(k.drivers.list())
        name = obj or args[0]
        drv = k.drivers.get(name)
        if not drv:
            return _err(f"Unknown driver: {name}. Known: {', '.join(k.drivers.names())}")

        # obj = driver name → first arg is action; else args[1] is action
        if obj and args:
            action = args[0]
        elif not obj and len(args) > 1:
            action = args[1]
        else:
            action = flags.get("action", "status")
        if action in ("info", "status", "probe", "read"):
            if action == "info":
                return drv.info()
            if action == "probe":
                return drv.probe()
            if action == "status":
                return drv.status()
            return drv.read(
                detail=flags.get("detail", "0") in ("1", "true", "yes"),
                path=flags.get("path"),
                sort=flags.get("sort", "cpu"),
                limit=int(flags.get("limit", "20")),
            )
        if action == "enable":
            deny = self.session.principal.require(CAP_DRIVER, CAP_SYS_ADMIN)
            if deny:
                return _err(deny)
            return drv.enable()
        if action == "disable":
            deny = self.session.principal.require(CAP_DRIVER, CAP_SYS_ADMIN)
            if deny:
                return _err(deny)
            return drv.disable()
        if action == "ioctl":
            req = flags.get("request") or (args[2] if len(args) > 2 else None)
            if not req:
                return _err("driver NAME ioctl request=...")
            return drv.ioctl(req, **{k2: v for k2, v in flags.items() if k2 != "request"})
        # default: read
        return drv.read(detail=flags.get("detail") in ("1", "true", "yes"))

    def _wifi_cmd(self, obj: Optional[str], args: List[str], flags: Dict[str, str]) -> Result:
        drv = self.kernel.drivers.get("wifi")
        if not drv:
            return _err("wifi driver missing")
        action = obj or (args[0] if args else "status")
        if action in ("status", "list", "info", "read"):
            return drv.read()
        if action == "scan":
            deny = self.session.principal.require(CAP_NET_RAW, CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            return drv.ioctl("scan", iface=flags.get("iface"))
        if action == "connect":
            deny = self.session.principal.require(CAP_NET_ADMIN, CAP_SYS_ADMIN)
            if deny:
                return _err(deny)
            ssid = flags.get("ssid") or (args[1] if len(args) > 1 else (args[0] if args and action != args[0] else None))
            # allow: wifi connect MySSID password=secret
            if not ssid and args:
                ssid = args[0] if action != "connect" else (args[1] if len(args) > 1 else args[0])
            return drv.ioctl("connect", ssid=ssid, password=flags.get("password"), iface=flags.get("iface"))
        if action == "disconnect":
            deny = self.session.principal.require(CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            return drv.ioctl("disconnect", iface=flags.get("iface"))
        if action in ("radio", "on", "off"):
            deny = self.session.principal.require(CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            state = "on" if action == "on" else ("off" if action == "off" else flags.get("state", "on"))
            return drv.ioctl("radio", state=state)
        return drv.read()

    def _bt_cmd(self, obj: Optional[str], args: List[str], flags: Dict[str, str]) -> Result:
        drv = self.kernel.drivers.get("bluetooth")
        if not drv:
            return _err("bluetooth driver missing")
        action = obj or (args[0] if args else "status")
        if action in ("status", "list", "info", "read"):
            return drv.read()
        if action == "scan":
            deny = self.session.principal.require(CAP_NET_RAW, CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            return drv.ioctl("scan", timeout=float(flags.get("timeout", "8")))
        if action == "power":
            deny = self.session.principal.require(CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            return drv.ioctl("power", state=flags.get("state", args[1] if len(args) > 1 else "on"))
        if action in ("pair", "connect", "disconnect"):
            deny = self.session.principal.require(CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            mac = flags.get("mac") or (args[1] if len(args) > 1 else (args[0] if args else None))
            return drv.ioctl(action, mac=mac)
        return drv.read()

    def _get(self, obj: Optional[str], args: List[str], flags: Dict[str, str]) -> Result:
        k = self.kernel
        detail = flags.get("detail", flags.get("d", "0")) in ("1", "true", "yes")
        if not obj:
            return k.snapshot()

        # map object → driver
        mapping = {
            "system": "system", "cpu": "cpu", "mem": "mem", "disk": "disk",
            "net": "net", "proc": "proc", "process": "proc",
            "sensors": "sensors", "battery": "battery", "thermal": "sensors",
            "usb": "usb", "pci": "pci", "routes": "routes", "arp": "arp",
            "dns": "dns", "wifi": "wifi", "bluetooth": "bluetooth",
            "hardware": "system",
        }
        name = mapping.get(obj)
        if name:
            drv = k.drivers.get(name)
            if not drv:
                return _err(f"Driver not loaded: {name}")
            if name == "proc" and args and args[0].isdigit():
                return drv.read(pid=int(args[0]))
            if name == "proc":
                return drv.read(
                    sort=flags.get("sort", flags.get("s", "cpu")),
                    limit=int(flags.get("limit", flags.get("n", "20"))),
                    user=flags.get("user", flags.get("u")),
                    name=flags.get("name") or (args[0] if args and not args[0].isdigit() else None),
                )
            if name == "disk":
                return drv.read(path=args[0] if args else flags.get("path"))
            if name in ("cpu", "net"):
                return drv.read(detail=detail)
            return drv.read()

        if obj.isdigit():
            drv = k.drivers.get("proc")
            return drv.read(pid=int(obj)) if drv else _err("proc driver missing")
        return _err(f"Unknown object: {obj}")

    def _help(self, topic: Optional[str] = None) -> Result:
        text = f"""
{SkylineKernel.NAME} Kernel  v{SkylineKernel.VERSION}
Userspace OS layer on Linux  •  Driver system  •  SKL language

DRIVERS (1.1)
  drivers                     List all drivers + probe status
  driver <name>               Read driver (status)
  driver <name> info|probe|status|read|enable|disable
  driver <name> ioctl request=... key=val

  Built-in drivers:
    system cpu mem disk net sensors battery usb pci
    routes arp dns wifi bluetooth proc

WIFI
  wifi / wifi status          Interfaces & connections
  wifi scan                   Scan access points
  wifi connect SSID [password=...]
  wifi disconnect
  wifi radio on|off

BLUETOOTH
  bluetooth / bt              Adapters & paired devices
  bt scan [timeout=8]
  bt power on|off
  bt pair MAC · bt connect MAC · bt disconnect MAC

SUDO
  sudo                        Elevate capabilities for ~5 minutes
  sudo for=15                 Elevate for 15 minutes
  sudo <command>              Elevate then run command
  unsudo                      Drop elevation
  whoami                      Shows sudo status

IDENTITY
  whoami · caps · role [name] · sessions · jobs · login ROLE

ENVIRONMENT
  pwd · cd · env · set · export · unset · echo · ls · cat · history

MONITOR
  get system|cpu|mem|disk|net|proc|sensors|usb|pci|routes|arp|dns|wifi|bluetooth
  get cpu detail=1 · get proc sort=mem limit=10 · snapshot

NETWORK
  ping HOST · resolve HOST · ifup IFACE · ifdown IFACE · sockets

PROCESS
  kill · terminate · forcekill · suspend · resume · renice · affinity

HOST
  exec · run · watch cpu,mem interval=1 · version · help

Permissions: monitor proc.self proc.other net.admin net.raw
             sys.nice sys.admin session env script driver sudo all
Roles: guest → user → operator → admin
"""
        return _ok(text.strip())


# ===========================================================================
# RENDERER (compact)
# ===========================================================================

class Renderer:
    def __init__(self, fmt: str = "pretty"):
        self.fmt = fmt

    def render(self, result: Result) -> str:
        if self.fmt == "json":
            return result.to_json()
        if not result.ok:
            return f"ERROR: {result.error}"
        if result.data is None:
            return "OK"
        if isinstance(result.data, str):
            return result.data
        if self.fmt == "raw":
            return str(result.data)
        return self._pretty(result)

    def _bar(self, pct: float, w: int = 16) -> str:
        filled = int(w * min(pct, 100) / 100)
        color = "green" if pct < 50 else "yellow" if pct < 80 else "red"
        return f"[{color}]{'█' * filled}{'░' * (w - filled)}[/{color}] {pct:5.1f}%"

    def _pretty(self, result: Result) -> str:
        if not RICH:
            return json.dumps(result.data, indent=2, default=str)
        data = result.data
        if isinstance(data, list) and data and isinstance(data[0], dict) and "category" in data[0] and "name" in data[0]:
            return self._drivers_table(data)
        if isinstance(data, dict) and "percent" in data and "cores_logical" in data:
            return self._kv("CPU", {
                "Usage": self._bar(data["percent"]),
                "Cores": f"{data.get('cores_physical')} phys / {data.get('cores_logical')} logical",
                "Freq": f"{data.get('freq_mhz')} MHz" if data.get("freq_mhz") else "—",
                "Loadavg": "  ".join(f"{x:.2f}" for x in (data.get("loadavg") or [])),
            })
        if isinstance(data, dict) and "ram" in data:
            r, s = data["ram"], data["swap"]
            t = Table(title="Memory", box=box.ROUNDED)
            t.add_column("Type", style="cyan")
            t.add_column("Total")
            t.add_column("Used")
            t.add_column("Avail")
            t.add_column("Usage")
            t.add_row("RAM", r["total_h"], r["used_h"], r["available_h"], self._bar(r["percent"]))
            t.add_row("Swap", s["total_h"], s["used_h"], _bytes_h(s.get("free", 0)),
                      self._bar(s["percent"]) if s["total"] else "—")
            with console.capture() as cap:
                console.print(t)
            return cap.get()
        if isinstance(data, list) and data and isinstance(data[0], dict) and "pid" in data[0]:
            t = Table(title="Processes", box=box.ROUNDED)
            t.add_column("PID", style="cyan", justify="right")
            t.add_column("User")
            t.add_column("Name", max_width=22)
            t.add_column("CPU%", justify="right")
            t.add_column("MEM%", justify="right")
            t.add_column("Status")
            for r in data:
                t.add_row(str(r["pid"]), (r.get("user") or "?")[:10],
                          (r.get("name") or "?")[:22], f"{r['cpu']:.1f}", f"{r['mem']:.1f}",
                          r.get("status") or "")
            with console.capture() as cap:
                console.print(t)
            return cap.get()
        if isinstance(data, dict) and "interfaces" in data and "connections" not in data or (
            isinstance(data, dict) and "interfaces" in data):
            # could be net or wifi
            if data["interfaces"] and isinstance(data["interfaces"][0], dict) and "name" in data["interfaces"][0]:
                t = Table(title="Network", box=box.ROUNDED)
                t.add_column("Iface", style="cyan")
                t.add_column("Up")
                t.add_column("RX")
                t.add_column("TX")
                for i in data["interfaces"]:
                    t.add_row(
                        i.get("name", "?"),
                        "[green]UP[/green]" if i.get("up") else "[red]DOWN[/red]",
                        i.get("rx_h", "—"), i.get("tx_h", "—"),
                    )
                with console.capture() as cap:
                    console.print(t)
                return cap.get()
        if result.meta.get("action"):
            return f"[OK] {result.meta['action']}: {json.dumps(data, default=str)}"
        if isinstance(data, dict):
            return self._kv("Result", {k: v for k, v in data.items() if not isinstance(v, (dict, list)) or k in ("user", "role", "session", "sudo")})
        return json.dumps(data, indent=2, default=str)

    def _kv(self, title: str, d: dict) -> str:
        t = Table(title=title, box=box.ROUNDED, show_header=False)
        t.add_column("Key", style="cyan", width=16)
        t.add_column("Value")
        for k, v in d.items():
            t.add_row(str(k), str(v))
        with console.capture() as cap:
            console.print(t)
        return cap.get()

    def _drivers_table(self, rows: list) -> str:
        t = Table(title="Skyline Drivers", box=box.ROUNDED)
        t.add_column("Name", style="cyan")
        t.add_column("Category")
        t.add_column("Available")
        t.add_column("Enabled")
        t.add_column("Description", max_width=36)
        for r in rows:
            avail = "[green]yes[/green]" if r.get("available") else "[red]no[/red]"
            en = "[green]yes[/green]" if r.get("enabled") else "[dim]no[/dim]"
            t.add_row(r["name"], r.get("category", ""), avail, en, r.get("description", "")[:36])
        with console.capture() as cap:
            console.print(t)
        return cap.get()


# ===========================================================================
# FRONTENDS
# ===========================================================================

HISTORY_FILE = os.path.expanduser("~/.skyline_history")


def run_repl(fmt: str = "pretty", role: str = "user"):
    kernel = SkylineKernel()
    session = kernel.new_session(role=role)
    exe = SKLExecutor(kernel, session)
    renderer = Renderer(fmt)

    banner = f"""
[bold blue]╔════════════════════════════════════════════╗
║       S K Y L I N E   K E R N E L  1.1     ║
║   drivers · wifi · bluetooth · sudo · SKL  ║
╚════════════════════════════════════════════╝[/bold blue]
[dim]user={session.principal.name}  role={session.principal.role}  session={session.principal.session_id}
type [green]help[/green] · [green]drivers[/green] · [green]whoami[/green] · [green]exit[/green][/dim]
"""
    if RICH:
        console.print(banner)
    else:
        print(f"Skyline Kernel v{SkylineKernel.VERSION}  role={session.principal.role}")

    session_ptk = None
    if PTK:
        words = list(SKLParser.VERBS) + list(SKLParser.OBJECTS) + kernel.drivers.names() + [
            "detail=1", "sort=cpu", "sort=mem", "limit=20", "interval=1",
            "count=3", "signal=TERM", "password=", "ssid=", "for=5",
        ]
        style = Style.from_dict({"prompt": "ansicyan bold"})
        session_ptk = PromptSession(
            history=FileHistory(HISTORY_FILE),
            auto_suggest=AutoSuggestFromHistory(),
            completer=WordCompleter(words, ignore_case=True),
            style=style,
        )

    while True:
        try:
            sudo_mark = "sudo:" if session.principal.sudo_active() else ""
            prompt_str = f"skyline:{sudo_mark}{session.principal.role}› "
            if session_ptk:
                line = session_ptk.prompt([("class:prompt", prompt_str)])
            else:
                line = input(prompt_str)
        except (EOFError, KeyboardInterrupt):
            print("\nlogout")
            break

        line = line.strip()
        if not line:
            continue
        if line.lower() in ("exit", "quit", "logout", "q"):
            print("logout")
            break
        if line.lower() == "clear":
            if RICH:
                console.clear()
            else:
                os.system("clear")
            continue

        session.history.append(line)
        stmts = exe.parser.parse(line)
        if stmts and stmts[0].verb == "watch":
            _run_watch(kernel, stmts[0])
            continue

        results = exe.run(line)
        for r in results:
            text = renderer.render(r)
            print(text, end="" if text.endswith("\n") else "\n")


def _run_watch(kernel: SkylineKernel, stmt: Statement):
    targets = (stmt.obj or "cpu,mem").split(",")
    interval = float(stmt.flags.get("interval", stmt.flags.get("i", "1")))
    print(f"watch {targets} every {interval}s  (Ctrl+C stop)")
    try:
        while True:
            bits = []
            for t in targets:
                t = t.strip()
                drv = kernel.drivers.get(t)
                if not drv:
                    continue
                r = drv.status()
                if not r.ok:
                    continue
                d = r.data
                if t == "cpu":
                    bits.append(f"CPU {d.get('percent', 0):5.1f}%")
                elif t == "mem":
                    bits.append(f"MEM {(d.get('ram') or {}).get('percent', 0):5.1f}%")
                elif t == "net":
                    rx = sum(i.get("rx", 0) for i in d.get("interfaces") or [])
                    tx = sum(i.get("tx", 0) for i in d.get("interfaces") or [])
                    bits.append(f"NET ↓{_bytes_h(rx)} ↑{_bytes_h(tx)}")
            print(f"\r[{datetime.now().strftime('%H:%M:%S')}]  " + "  │  ".join(bits) + "   ", end="", flush=True)
            time.sleep(interval)
    except KeyboardInterrupt:
        print("\nstopped")


def run_oneshot(code: str, fmt: str = "json", role: str = "user"):
    kernel = SkylineKernel()
    session = kernel.new_session(role=role)
    exe = SKLExecutor(kernel, session)
    renderer = Renderer(fmt)
    results = exe.run(code)
    for r in results:
        print(renderer.render(r))
        if not r.ok:
            sys.exit(1)


def run_server(host: str = "127.0.0.1", port: int = 7420, role: str = "user"):
    kernel = SkylineKernel()
    srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind((host, port))
    srv.listen(16)
    print(f"Skyline {kernel.VERSION} server {host}:{port}", flush=True)

    def handle(conn: socket.socket, addr):
        session = kernel.new_session(role=role)
        exe = SKLExecutor(kernel, session)
        print(f"+ {addr} session={session.principal.session_id}", flush=True)
        with conn:
            buf = b""
            while True:
                try:
                    chunk = conn.recv(8192)
                except ConnectionResetError:
                    break
                if not chunk:
                    break
                buf += chunk
                while b"\n" in buf:
                    raw, buf = buf.split(b"\n", 1)
                    text = raw.decode("utf-8", errors="replace").strip()
                    if not text:
                        continue
                    if text.lower() in ("quit", "exit", "logout"):
                        conn.sendall(b'{"ok":true,"data":"logout"}\n')
                        return
                    for r in exe.run(text):
                        conn.sendall((r.to_json(indent=None) + "\n").encode())
        print(f"- {addr}", flush=True)

    while True:
        conn, addr = srv.accept()
        threading.Thread(target=handle, args=(conn, addr), daemon=True).start()


def main():
    ap = argparse.ArgumentParser(
        description="Skyline Kernel 1.1 — drivers, wifi, bluetooth, sudo, SKL",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s
  %(prog)s -c "drivers; get cpu; wifi; sudo; whoami"
  %(prog)s -c "driver wifi scan" --json
  %(prog)s --server --port 7420
        """,
    )
    ap.add_argument("-c", "--command", help="Run SKL and exit (- = stdin)")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--raw", action="store_true")
    ap.add_argument("--server", action="store_true")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=7420)
    ap.add_argument("--role", default="user", choices=list(ROLES.keys()))
    args = ap.parse_args()

    fmt = "json" if args.json else ("raw" if args.raw else "pretty")
    if args.server:
        run_server(args.host, args.port, role=args.role)
        return
    if args.command is not None:
        code = sys.stdin.read() if args.command == "-" else args.command
        run_oneshot(code, fmt=fmt, role=args.role)
        return
    run_repl(fmt=fmt, role=args.role)


if __name__ == "__main__":
    main()
#!/usr/bin/env python3
"""
Skyline Kernel  v1.1
====================
Userspace OS layer on top of Linux.

  • Driver system   – pluggable drivers for every hardware/network component
  • Networking      – Wi‑Fi, Bluetooth, routes, ARP, sockets, DNS, ping
  • Permissions     – capabilities + roles + sudo elevation
  • SKL language    – expanded shell language for all frontends
  • Sessions        – env, cwd, jobs, variables

A shell built on Skyline can act as a full interactive environment
while the host Linux continues to run underneath.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import pwd
import re
import signal
import socket
import struct
import subprocess
import sys
import threading
import time
import uuid
from abc import ABC, abstractmethod
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

# ---------------------------------------------------------------------------
# Dependencies
# ---------------------------------------------------------------------------
try:
    import psutil
except ImportError:
    print("FATAL: psutil required → pip install psutil", file=sys.stderr)
    sys.exit(1)

try:
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    from rich import box
    RICH = True
    console = Console()
except ImportError:
    RICH = False
    console = None

try:
    from prompt_toolkit import PromptSession
    from prompt_toolkit.history import FileHistory
    from prompt_toolkit.auto_suggest import AutoSuggestFromHistory
    from prompt_toolkit.completion import WordCompleter
    from prompt_toolkit.styles import Style
    PTK = True
except ImportError:
    PTK = False


# ===========================================================================
# RESULT
# ===========================================================================

@dataclass
class Result:
    ok: bool = True
    data: Any = None
    error: Optional[str] = None
    meta: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict:
        return {"ok": self.ok, "data": self.data, "error": self.error, "meta": self.meta}

    def to_json(self, indent: Optional[int] = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent, default=str)


def _ok(data: Any = None, **meta) -> Result:
    return Result(ok=True, data=data, meta=meta)


def _err(msg: str, **meta) -> Result:
    return Result(ok=False, error=msg, meta=meta)


def _bytes_h(n: int | float) -> str:
    n = float(n)
    for u in ("B", "KB", "MB", "GB", "TB", "PB"):
        if abs(n) < 1024:
            return f"{n:.1f} {u}"
        n /= 1024
    return f"{n:.1f} EB"


def _run(cmd: List[str], timeout: float = 15) -> Tuple[int, str, str]:
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout.strip(), r.stderr.strip()
    except FileNotFoundError:
        return 127, "", f"not found: {cmd[0]}"
    except subprocess.TimeoutExpired:
        return 124, "", "timeout"
    except Exception as e:
        return 1, "", str(e)


def _which(name: str) -> Optional[str]:
    for d in os.environ.get("PATH", "").split(":"):
        p = os.path.join(d, name)
        if os.path.isfile(p) and os.access(p, os.X_OK):
            return p
    return None


# ===========================================================================
# PERMISSIONS
# ===========================================================================

CAP_MONITOR    = "monitor"
CAP_PROC_SELF  = "proc.self"
CAP_PROC_OTHER = "proc.other"
CAP_NET_ADMIN  = "net.admin"
CAP_NET_RAW    = "net.raw"       # ping, bluetooth scan, wifi scan
CAP_SYS_NICE   = "sys.nice"
CAP_SYS_ADMIN  = "sys.admin"
CAP_SESSION    = "session"
CAP_ENV        = "env"
CAP_SCRIPT     = "script"
CAP_DRIVER     = "driver"        # load/unload / driver control
CAP_SUDO       = "sudo"          # may request elevation
CAP_ALL        = "all"

ALL_CAPS = {
    CAP_MONITOR, CAP_PROC_SELF, CAP_PROC_OTHER, CAP_NET_ADMIN, CAP_NET_RAW,
    CAP_SYS_NICE, CAP_SYS_ADMIN, CAP_SESSION, CAP_ENV, CAP_SCRIPT,
    CAP_DRIVER, CAP_SUDO, CAP_ALL,
}

ROLES: Dict[str, Set[str]] = {
    "guest":    {CAP_MONITOR},
    "user":     {CAP_MONITOR, CAP_PROC_SELF, CAP_ENV, CAP_SCRIPT, CAP_NET_RAW, CAP_SUDO},
    "operator": {
        CAP_MONITOR, CAP_PROC_SELF, CAP_PROC_OTHER, CAP_SYS_NICE,
        CAP_ENV, CAP_SCRIPT, CAP_NET_ADMIN, CAP_NET_RAW, CAP_DRIVER, CAP_SUDO,
    },
    "admin":    ALL_CAPS.copy(),
}


@dataclass
class Principal:
    name: str
    role: str = "user"
    caps: Set[str] = field(default_factory=set)
    host_uid: Optional[int] = None
    host_user: Optional[str] = None
    session_id: str = field(default_factory=lambda: uuid.uuid4().hex[:12])
    created: str = field(default_factory=lambda: datetime.now().isoformat(timespec="seconds"))
    # sudo state
    sudo_until: Optional[datetime] = None
    sudo_caps: Set[str] = field(default_factory=set)

    def __post_init__(self):
        if not self.caps:
            self.caps = set(ROLES.get(self.role, ROLES["user"]))
        if CAP_ALL in self.caps:
            self.caps = ALL_CAPS.copy()

    def effective_caps(self) -> Set[str]:
        caps = set(self.caps)
        if self.sudo_until and datetime.now() < self.sudo_until:
            caps |= self.sudo_caps
            if CAP_ALL in caps:
                return ALL_CAPS.copy()
        return caps

    def has(self, *needed: str) -> bool:
        caps = self.effective_caps()
        if CAP_ALL in caps:
            return True
        return any(c in caps for c in needed)

    def require(self, *needed: str) -> Optional[str]:
        if self.has(*needed):
            return None
        return f"permission denied: need one of {needed} (role={self.role}, sudo={'yes' if self.sudo_active() else 'no'})"

    def sudo_active(self) -> bool:
        return bool(self.sudo_until and datetime.now() < self.sudo_until)

    def grant_sudo(self, minutes: float = 5.0, extra: Optional[Set[str]] = None):
        self.sudo_until = datetime.now() + timedelta(minutes=minutes)
        self.sudo_caps = set(extra or ALL_CAPS)

    def drop_sudo(self):
        self.sudo_until = None
        self.sudo_caps = set()


# ===========================================================================
# SESSION
# ===========================================================================

@dataclass
class Job:
    jid: int
    pid: int
    cmd: str
    status: str = "running"
    bg: bool = True


class Session:
    _next_jid = 1

    def __init__(self, principal: Principal):
        self.principal = principal
        self.env: Dict[str, str] = {
            "SKL_USER": principal.name,
            "SKL_ROLE": principal.role,
            "SKL_SESSION": principal.session_id,
            "SKL_HOME": str(Path.home()),
            "SKL_HOST": socket.gethostname(),
            "SKL_VERSION": "1.1.0",
            "PATH": os.environ.get("PATH", ""),
            "PWD": os.getcwd(),
            "TERM": os.environ.get("TERM", "xterm-256color"),
        }
        self.cwd = os.getcwd()
        self.jobs: Dict[int, Job] = {}
        self.vars: Dict[str, str] = {}
        self.last_result: Optional[Result] = None
        self.history: List[str] = []

    def export(self, key: str, value: str):
        self.env[key] = value
        if key == "PWD":
            self.cwd = value

    def getvar(self, name: str) -> Optional[str]:
        return self.vars.get(name) or self.env.get(name) or os.environ.get(name)

    def setvar(self, name: str, value: str):
        self.vars[name] = value

    def add_job(self, pid: int, cmd: str, bg: bool = True) -> int:
        jid = Session._next_jid
        Session._next_jid += 1
        self.jobs[jid] = Job(jid=jid, pid=pid, cmd=cmd, bg=bg)
        return jid

    def refresh_jobs(self):
        for job in self.jobs.values():
            try:
                p = psutil.Process(job.pid)
                st = p.status()
                if st == psutil.STATUS_STOPPED:
                    job.status = "stopped"
                elif st in (psutil.STATUS_ZOMBIE, psutil.STATUS_DEAD):
                    job.status = "done"
                else:
                    job.status = "running"
            except psutil.NoSuchProcess:
                job.status = "done"


# ===========================================================================
# DRIVER SYSTEM  (Skyline 1.1)
# ===========================================================================

class Driver(ABC):
    """Base class for every Skyline component driver."""

    name: str = "base"
    description: str = ""
    version: str = "1.1"
    category: str = "system"   # system | hardware | network | wireless | power | input
    requires_caps: Set[str] = field(default_factory=lambda: {CAP_MONITOR})

    def __init__(self, kernel: "SkylineKernel"):
        self.kernel = kernel
        self.loaded = True
        self.enabled = True
        self._meta: Dict[str, Any] = {}

    @abstractmethod
    def probe(self) -> Result:
        """Detect whether this driver can operate on the host."""
        ...

    @abstractmethod
    def status(self) -> Result:
        """Current operational status / summary."""
        ...

    def info(self) -> Result:
        return _ok({
            "name": self.name,
            "description": self.description,
            "version": self.version,
            "category": self.category,
            "loaded": self.loaded,
            "enabled": self.enabled,
            "requires_caps": sorted(self.requires_caps),
            "meta": self._meta,
        })

    def enable(self) -> Result:
        self.enabled = True
        return _ok({"name": self.name, "enabled": True}, action="enable")

    def disable(self) -> Result:
        self.enabled = False
        return _ok({"name": self.name, "enabled": False}, action="disable")

    def read(self, **kwargs) -> Result:
        """Default read → status. Override for rich data."""
        return self.status()

    def write(self, **kwargs) -> Result:
        return _err(f"Driver '{self.name}' does not support write")

    def ioctl(self, request: str, **kwargs) -> Result:
        """Driver-specific control plane."""
        return _err(f"Unknown ioctl '{request}' for driver '{self.name}'")


class DriverRegistry:
    def __init__(self, kernel: "SkylineKernel"):
        self.kernel = kernel
        self._drivers: Dict[str, Driver] = {}

    def register(self, driver: Driver):
        self._drivers[driver.name] = driver

    def get(self, name: str) -> Optional[Driver]:
        return self._drivers.get(name)

    def list(self) -> List[dict]:
        out = []
        for d in sorted(self._drivers.values(), key=lambda x: (x.category, x.name)):
            probe = d.probe()
            out.append({
                "name": d.name,
                "category": d.category,
                "description": d.description,
                "loaded": d.loaded,
                "enabled": d.enabled,
                "available": probe.ok,
                "probe": probe.data if probe.ok else probe.error,
            })
        return out

    def names(self) -> List[str]:
        return sorted(self._drivers.keys())


# ----- concrete drivers ----------------------------------------------------

class CpuDriver(Driver):
    name = "cpu"
    description = "CPU usage, frequency, per-core, load average"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def __init__(self, kernel):
        super().__init__(kernel)
        self._primed = False

    def _prime(self):
        if not self._primed:
            psutil.cpu_percent(interval=None)
            self._primed = True

    def probe(self) -> Result:
        return _ok({"cores": psutil.cpu_count(), "freq": bool(psutil.cpu_freq())})

    def status(self) -> Result:
        self._prime()
        pct = psutil.cpu_percent(interval=0.15)
        freq = psutil.cpu_freq()
        return _ok({
            "percent": pct,
            "cores_physical": psutil.cpu_count(logical=False) or 0,
            "cores_logical": psutil.cpu_count(logical=True) or 0,
            "freq_mhz": round(freq.current, 1) if freq else None,
            "loadavg": list(os.getloadavg()) if hasattr(os, "getloadavg") else None,
        })

    def read(self, detail: bool = False, **_) -> Result:
        self._prime()
        base = self.status().data
        if detail:
            base["per_core"] = psutil.cpu_percent(interval=0.12, percpu=True)
            times = psutil.cpu_times_percent(interval=0.1)
            base["times"] = {
                "user": times.user, "system": times.system, "idle": times.idle,
                "iowait": getattr(times, "iowait", 0), "irq": getattr(times, "irq", 0),
                "softirq": getattr(times, "softirq", 0),
            }
            try:
                base["stats"] = dict(psutil.cpu_stats()._asdict())
            except Exception:
                pass
        return _ok(base)


class MemDriver(Driver):
    name = "mem"
    description = "RAM and swap memory"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"total": psutil.virtual_memory().total})

    def status(self) -> Result:
        vm = psutil.virtual_memory()
        sm = psutil.swap_memory()
        return _ok({
            "ram": {
                "total": vm.total, "used": vm.used, "available": vm.available,
                "percent": vm.percent,
                "cached": getattr(vm, "cached", 0), "buffers": getattr(vm, "buffers", 0),
                "total_h": _bytes_h(vm.total), "used_h": _bytes_h(vm.used),
                "available_h": _bytes_h(vm.available),
            },
            "swap": {
                "total": sm.total, "used": sm.used, "free": sm.free, "percent": sm.percent,
                "total_h": _bytes_h(sm.total), "used_h": _bytes_h(sm.used),
            },
        })

    def read(self, **_) -> Result:
        return self.status()


class DiskDriver(Driver):
    name = "disk"
    description = "Block devices, partitions, I/O counters"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"partitions": len(psutil.disk_partitions(all=False))})

    def status(self) -> Result:
        return self.read()

    def read(self, path: Optional[str] = None, **_) -> Result:
        parts = []
        for p in psutil.disk_partitions(all=False):
            try:
                u = psutil.disk_usage(p.mountpoint)
            except (PermissionError, OSError):
                continue
            parts.append({
                "device": p.device, "mount": p.mountpoint, "fstype": p.fstype, "opts": p.opts,
                "total": u.total, "used": u.used, "free": u.free, "percent": u.percent,
                "total_h": _bytes_h(u.total), "used_h": _bytes_h(u.used), "free_h": _bytes_h(u.free),
            })
        io = None
        try:
            c = psutil.disk_io_counters()
            if c:
                io = {
                    "read_bytes": c.read_bytes, "write_bytes": c.write_bytes,
                    "read_count": c.read_count, "write_count": c.write_count,
                    "read_h": _bytes_h(c.read_bytes), "write_h": _bytes_h(c.write_bytes),
                }
        except Exception:
            pass
        usage = None
        if path:
            try:
                u = psutil.disk_usage(path)
                usage = {
                    "path": path, "total": u.total, "used": u.used, "free": u.free,
                    "percent": u.percent, "total_h": _bytes_h(u.total),
                    "used_h": _bytes_h(u.used), "free_h": _bytes_h(u.free),
                }
            except Exception as e:
                return _err(str(e))
        return _ok({"partitions": parts, "io": io, "path_usage": usage})


class NetDriver(Driver):
    name = "net"
    description = "Network interfaces, traffic, connections"
    category = "network"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"interfaces": list(psutil.net_if_addrs().keys())})

    def status(self) -> Result:
        return self.read(detail=False)

    def read(self, detail: bool = False, **_) -> Result:
        addrs = psutil.net_if_addrs()
        stats = psutil.net_if_stats()
        io = psutil.net_io_counters(pernic=True)
        ifaces = []
        for name, alist in sorted(addrs.items()):
            st = stats.get(name)
            ips = []
            for a in alist:
                if a.family == socket.AF_INET:
                    ips.append({"family": "inet", "addr": a.address, "netmask": a.netmask,
                                "broadcast": a.broadcast})
                elif a.family == socket.AF_INET6 and not a.address.startswith("fe80"):
                    ips.append({"family": "inet6", "addr": a.address})
                elif getattr(a.family, "name", "") == "AF_LINK" or a.family == 17:
                    ips.append({"family": "mac", "addr": a.address})
            entry: Dict[str, Any] = {
                "name": name, "up": bool(st and st.isup),
                "speed_mbps": st.speed if st else 0, "mtu": st.mtu if st else None,
                "addrs": ips,
            }
            if name in io:
                c = io[name]
                entry.update({
                    "rx": c.bytes_recv, "tx": c.bytes_sent,
                    "rx_h": _bytes_h(c.bytes_recv), "tx_h": _bytes_h(c.bytes_sent),
                    "packets_rx": c.packets_recv, "packets_tx": c.packets_sent,
                    "errin": c.errin, "errout": c.errout,
                    "dropin": c.dropin, "dropout": c.dropout,
                })
            ifaces.append(entry)
        data: Dict[str, Any] = {"interfaces": ifaces}
        if detail:
            conns = []
            for c in psutil.net_connections(kind="inet"):
                conns.append({
                    "fd": c.fd,
                    "type": c.type.name if hasattr(c.type, "name") else str(c.type),
                    "laddr": f"{c.laddr.ip}:{c.laddr.port}" if c.laddr else None,
                    "raddr": f"{c.raddr.ip}:{c.raddr.port}" if c.raddr else None,
                    "status": c.status, "pid": c.pid,
                })
            data["connections"] = conns
            data["connection_count"] = len(conns)
            data["listening"] = [c for c in conns if c["status"] == "LISTEN"]
        return _ok(data)

    def ioctl(self, request: str, **kwargs) -> Result:
        name = kwargs.get("iface") or kwargs.get("name")
        if request == "up":
            if not name:
                return _err("iface required")
            code, out, err = _run(["ip", "link", "set", name, "up"])
            return _ok({"iface": name, "stdout": out}) if code == 0 else _err(err or out)
        if request == "down":
            if not name:
                return _err("iface required")
            code, out, err = _run(["ip", "link", "set", name, "down"])
            return _ok({"iface": name, "stdout": out}) if code == 0 else _err(err or out)
        return _err(f"Unknown net ioctl: {request}")


class SensorsDriver(Driver):
    name = "sensors"
    description = "Temperatures, fans, thermal zones"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        has = False
        try:
            if psutil.sensors_temperatures():
                has = True
        except Exception:
            pass
        if Path("/sys/class/thermal").exists():
            has = True
        return _ok({"available": has}) if has else _err("No sensors")

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        data: Dict[str, Any] = {}
        try:
            temps = psutil.sensors_temperatures()
            if temps:
                data["temps"] = {
                    n: [{"label": e.label, "current": e.current, "high": e.high, "critical": e.critical}
                        for e in ents]
                    for n, ents in temps.items()
                }
        except Exception:
            pass
        try:
            fans = psutil.sensors_fans()
            if fans:
                data["fans"] = {
                    n: [{"label": e.label, "rpm": e.current} for e in ents]
                    for n, ents in fans.items()
                }
        except Exception:
            pass
        zones = []
        base = Path("/sys/class/thermal")
        if base.exists():
            for d in sorted(base.glob("thermal_zone*")):
                try:
                    t = (d / "temp").read_text().strip()
                    typ = (d / "type").read_text().strip() if (d / "type").exists() else d.name
                    zones.append({"zone": d.name, "type": typ, "temp_c": int(t) / 1000.0})
                except Exception:
                    continue
        if zones:
            data["thermal_zones"] = zones
        return _ok(data) if data else _err("No sensor data")


class BatteryDriver(Driver):
    name = "battery"
    description = "Battery / power supply"
    category = "power"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        try:
            b = psutil.sensors_battery()
            return _ok({"present": b is not None})
        except Exception:
            return _err("unsupported")

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        try:
            bat = psutil.sensors_battery()
        except Exception:
            bat = None
        if not bat:
            # sysfs fallback
            ps = Path("/sys/class/power_supply")
            if ps.exists():
                supplies = []
                for d in ps.iterdir():
                    try:
                        t = (d / "type").read_text().strip() if (d / "type").exists() else "?"
                        supplies.append({"name": d.name, "type": t})
                    except Exception:
                        continue
                return _ok({"supplies": supplies}) if supplies else _err("No battery")
            return _err("No battery")
        return _ok({
            "percent": bat.percent, "plugged": bat.power_plugged,
            "secsleft": bat.secsleft if bat.secsleft not in (
                psutil.POWER_TIME_UNLIMITED, psutil.POWER_TIME_UNKNOWN, -1) else None,
        })


class UsbDriver(Driver):
    name = "usb"
    description = "USB devices (sysfs + lsusb)"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"sysfs": Path("/sys/bus/usb/devices").exists()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        devices = []
        usb_base = Path("/sys/bus/usb/devices")
        if usb_base.exists():
            for d in usb_base.iterdir():
                if ":" in d.name:
                    continue
                try:
                    vendor = (d / "idVendor").read_text().strip() if (d / "idVendor").exists() else None
                    product = (d / "idProduct").read_text().strip() if (d / "idProduct").exists() else None
                    manu = (d / "manufacturer").read_text().strip() if (d / "manufacturer").exists() else None
                    prod = (d / "product").read_text().strip() if (d / "product").exists() else None
                    if vendor or product:
                        devices.append({
                            "sysfs": d.name, "vendor_id": vendor, "product_id": product,
                            "manufacturer": manu, "product": prod,
                        })
                except Exception:
                    continue
        if not devices:
            code, out, _ = _run(["lsusb"])
            if code == 0:
                devices = [{"raw": ln} for ln in out.splitlines() if ln]
        return _ok(devices) if devices else _err("No USB info")


class PciDriver(Driver):
    name = "pci"
    description = "PCI devices (lspci)"
    category = "hardware"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"lspci": bool(_which("lspci"))})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        code, out, err = _run(["lspci", "-mm"])
        if code != 0:
            code, out, err = _run(["lspci"])
        if code != 0:
            return _err(err or "lspci failed")
        return _ok([ln for ln in out.splitlines() if ln])


class RoutesDriver(Driver):
    name = "routes"
    description = "IPv4 routing table"
    category = "network"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"proc": Path("/proc/net/route").exists()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        routes = []
        try:
            with open("/proc/net/route") as f:
                next(f)
                for line in f:
                    parts = line.split()
                    if len(parts) < 8:
                        continue
                    iface, dest, gateway, flags, _, _, _, mask = parts[:8]
                    routes.append({
                        "iface": iface,
                        "destination": self._hex_ip(dest),
                        "gateway": self._hex_ip(gateway),
                        "mask": self._hex_ip(mask),
                        "flags": flags,
                    })
        except Exception as e:
            return _err(str(e))
        return _ok(routes)

    @staticmethod
    def _hex_ip(h: str) -> str:
        try:
            return socket.inet_ntoa(struct.pack("<L", int(h, 16)))
        except Exception:
            return h


class ArpDriver(Driver):
    name = "arp"
    description = "ARP neighbour table"
    category = "network"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"proc": Path("/proc/net/arp").exists()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        entries = []
        try:
            with open("/proc/net/arp") as f:
                next(f)
                for line in f:
                    parts = line.split()
                    if len(parts) >= 6:
                        entries.append({
                            "ip": parts[0], "hwtype": parts[1], "flags": parts[2],
                            "mac": parts[3], "mask": parts[4], "device": parts[5],
                        })
        except Exception as e:
            return _err(str(e))
        return _ok(entries)


class DnsDriver(Driver):
    name = "dns"
    description = "Resolver configuration"
    category = "network"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"resolv": Path("/etc/resolv.conf").exists()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        resolv = []
        try:
            with open("/etc/resolv.conf") as f:
                for line in f:
                    line = line.strip()
                    if line.startswith("nameserver"):
                        resolv.append(line.split()[1])
        except Exception:
            pass
        hosts = []
        try:
            with open("/etc/hosts") as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        hosts.append(line)
        except Exception:
            pass
        return _ok({"nameservers": resolv, "hosts_sample": hosts[:20]})


class WifiDriver(Driver):
    """Wi‑Fi via nmcli / iw / iwconfig / sysfs."""
    name = "wifi"
    description = "Wi‑Fi interfaces, scan, connection status"
    category = "wireless"
    requires_caps = {CAP_MONITOR, CAP_NET_RAW}

    def probe(self) -> Result:
        tools = {t: bool(_which(t)) for t in ("nmcli", "iw", "iwconfig", "wpa_cli")}
        wireless = []
        net = Path("/sys/class/net")
        if net.exists():
            for iface in net.iterdir():
                if (iface / "wireless").exists() or (iface / "phy80211").exists():
                    wireless.append(iface.name)
        available = any(tools.values()) or bool(wireless)
        return _ok({"tools": tools, "wireless_ifaces": wireless, "available": available}) \
            if available else _err("No Wi‑Fi support detected")

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        data: Dict[str, Any] = {"interfaces": [], "connections": [], "scan": []}

        # nmcli device
        if _which("nmcli"):
            code, out, _ = _run(["nmcli", "-t", "-f", "DEVICE,TYPE,STATE,CONNECTION", "device"])
            if code == 0:
                for ln in out.splitlines():
                    parts = ln.split(":")
                    if len(parts) >= 4 and parts[1] == "wifi":
                        data["interfaces"].append({
                            "device": parts[0], "type": parts[1],
                            "state": parts[2], "connection": parts[3] or None,
                        })
            code, out, _ = _run(["nmcli", "-t", "-f", "NAME,UUID,TYPE,DEVICE", "connection", "show"])
            if code == 0:
                for ln in out.splitlines():
                    parts = ln.split(":")
                    if len(parts) >= 4 and "wireless" in parts[2]:
                        data["connections"].append({
                            "name": parts[0], "uuid": parts[1],
                            "type": parts[2], "device": parts[3] or None,
                        })

        # iw dev
        if not data["interfaces"] and _which("iw"):
            code, out, _ = _run(["iw", "dev"])
            if code == 0:
                current = None
                for ln in out.splitlines():
                    ln = ln.strip()
                    if ln.startswith("Interface "):
                        current = {"device": ln.split()[1]}
                        data["interfaces"].append(current)
                    elif current and ln.startswith("type "):
                        current["type"] = ln.split()[1]
                    elif current and ln.startswith("ssid "):
                        current["ssid"] = ln[5:]

        # sysfs fallback
        if not data["interfaces"]:
            net = Path("/sys/class/net")
            if net.exists():
                for iface in net.iterdir():
                    if (iface / "wireless").exists() or (iface / "phy80211").exists():
                        data["interfaces"].append({"device": iface.name, "source": "sysfs"})

        return _ok(data)

    def ioctl(self, request: str, **kwargs) -> Result:
        if request == "scan":
            return self._scan(kwargs.get("iface"))
        if request == "connect":
            ssid = kwargs.get("ssid")
            password = kwargs.get("password")
            if not ssid:
                return _err("ssid required")
            return self._connect(ssid, password, kwargs.get("iface"))
        if request == "disconnect":
            return self._disconnect(kwargs.get("iface"))
        if request == "radio":
            state = kwargs.get("state", "on")
            return self._radio(state)
        return _err(f"Unknown wifi ioctl: {request}")

    def _scan(self, iface: Optional[str] = None) -> Result:
        if _which("nmcli"):
            code, out, err = _run(["nmcli", "-t", "-f", "SSID,SIGNAL,SECURITY,CHAN,BARS", "device", "wifi", "list"], timeout=30)
            if code == 0:
                aps = []
                for ln in out.splitlines():
                    parts = ln.split(":")
                    if len(parts) >= 3:
                        aps.append({
                            "ssid": parts[0], "signal": parts[1],
                            "security": parts[2], "channel": parts[3] if len(parts) > 3 else None,
                        })
                return _ok(aps)
            return _err(err or "nmcli scan failed")
        if _which("iw") and iface:
            code, out, err = _run(["iw", "dev", iface, "scan"], timeout=30)
            if code == 0:
                return _ok({"raw": out[:5000]})
            return _err(err or "iw scan failed")
        return _err("No Wi‑Fi scan tool available (need nmcli or iw)")

    def _connect(self, ssid: str, password: Optional[str], iface: Optional[str]) -> Result:
        if not _which("nmcli"):
            return _err("nmcli required for connect")
        cmd = ["nmcli", "device", "wifi", "connect", ssid]
        if password:
            cmd += ["password", password]
        if iface:
            cmd += ["ifname", iface]
        code, out, err = _run(cmd, timeout=45)
        return _ok({"ssid": ssid, "stdout": out}) if code == 0 else _err(err or out)

    def _disconnect(self, iface: Optional[str]) -> Result:
        if not _which("nmcli"):
            return _err("nmcli required")
        target = iface or "wifi"
        code, out, err = _run(["nmcli", "device", "disconnect", target])
        return _ok({"stdout": out}) if code == 0 else _err(err or out)

    def _radio(self, state: str) -> Result:
        if _which("nmcli"):
            code, out, err = _run(["nmcli", "radio", "wifi", state])
            return _ok({"radio": state, "stdout": out}) if code == 0 else _err(err or out)
        if _which("rfkill"):
            action = "unblock" if state in ("on", "enable") else "block"
            code, out, err = _run(["rfkill", action, "wifi"])
            return _ok({"radio": state}) if code == 0 else _err(err or out)
        return _err("No radio control tool")


class BluetoothDriver(Driver):
    """Bluetooth via bluetoothctl / hciconfig / sysfs."""
    name = "bluetooth"
    description = "Bluetooth adapters, devices, scan"
    category = "wireless"
    requires_caps = {CAP_MONITOR, CAP_NET_RAW}

    def probe(self) -> Result:
        tools = {t: bool(_which(t)) for t in ("bluetoothctl", "hciconfig", "btmgmt")}
        sysfs = Path("/sys/class/bluetooth").exists()
        available = any(tools.values()) or sysfs
        return _ok({"tools": tools, "sysfs": sysfs, "available": available}) \
            if available else _err("No Bluetooth support detected")

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        data: Dict[str, Any] = {"adapters": [], "devices": []}

        if _which("bluetoothctl"):
            code, out, _ = _run(["bluetoothctl", "list"])
            if code == 0:
                for ln in out.splitlines():
                    # Controller XX:XX:XX:XX:XX:XX Name
                    parts = ln.split()
                    if len(parts) >= 2 and parts[0] == "Controller":
                        data["adapters"].append({
                            "mac": parts[1],
                            "name": " ".join(parts[2:]) if len(parts) > 2 else None,
                        })
            code, out, _ = _run(["bluetoothctl", "devices"])
            if code == 0:
                for ln in out.splitlines():
                    parts = ln.split()
                    if len(parts) >= 2 and parts[0] == "Device":
                        data["devices"].append({
                            "mac": parts[1],
                            "name": " ".join(parts[2:]) if len(parts) > 2 else None,
                        })

        if not data["adapters"] and _which("hciconfig"):
            code, out, _ = _run(["hciconfig"])
            if code == 0:
                data["adapters_raw"] = out

        if not data["adapters"]:
            bt = Path("/sys/class/bluetooth")
            if bt.exists():
                for d in bt.iterdir():
                    data["adapters"].append({"sysfs": d.name})

        return _ok(data)

    def ioctl(self, request: str, **kwargs) -> Result:
        if request == "scan":
            return self._scan(kwargs.get("timeout", 8))
        if request == "power":
            return self._power(kwargs.get("state", "on"))
        if request == "pair":
            mac = kwargs.get("mac")
            if not mac:
                return _err("mac required")
            return self._pair(mac)
        if request == "connect":
            mac = kwargs.get("mac")
            if not mac:
                return _err("mac required")
            return self._connect(mac)
        if request == "disconnect":
            mac = kwargs.get("mac")
            if not mac:
                return _err("mac required")
            return self._disconnect(mac)
        return _err(f"Unknown bluetooth ioctl: {request}")

    def _scan(self, timeout: float = 8) -> Result:
        if not _which("bluetoothctl"):
            return _err("bluetoothctl required for scan")
        # non-interactive scan
        code, out, err = _run(
            ["bluetoothctl", "--timeout", str(int(timeout)), "scan", "on"],
            timeout=timeout + 5,
        )
        # list discovered
        code2, out2, _ = _run(["bluetoothctl", "devices"])
        devices = []
        if code2 == 0:
            for ln in out2.splitlines():
                parts = ln.split()
                if len(parts) >= 2 and parts[0] == "Device":
                    devices.append({"mac": parts[1], "name": " ".join(parts[2:]) if len(parts) > 2 else None})
        return _ok({"devices": devices, "scan_output": out[:2000]})

    def _power(self, state: str) -> Result:
        if _which("bluetoothctl"):
            onoff = "on" if state in ("on", "enable", "1") else "off"
            code, out, err = _run(["bluetoothctl", "power", onoff])
            return _ok({"power": onoff, "stdout": out}) if code == 0 else _err(err or out)
        if _which("rfkill"):
            action = "unblock" if state in ("on", "enable", "1") else "block"
            code, out, err = _run(["rfkill", action, "bluetooth"])
            return _ok({"power": state}) if code == 0 else _err(err or out)
        return _err("No Bluetooth power control")

    def _pair(self, mac: str) -> Result:
        if not _which("bluetoothctl"):
            return _err("bluetoothctl required")
        code, out, err = _run(["bluetoothctl", "pair", mac], timeout=30)
        return _ok({"mac": mac, "stdout": out}) if code == 0 else _err(err or out)

    def _connect(self, mac: str) -> Result:
        if not _which("bluetoothctl"):
            return _err("bluetoothctl required")
        code, out, err = _run(["bluetoothctl", "connect", mac], timeout=20)
        return _ok({"mac": mac, "stdout": out}) if code == 0 else _err(err or out)

    def _disconnect(self, mac: str) -> Result:
        if not _which("bluetoothctl"):
            return _err("bluetoothctl required")
        code, out, err = _run(["bluetoothctl", "disconnect", mac])
        return _ok({"mac": mac, "stdout": out}) if code == 0 else _err(err or out)


class ProcessDriver(Driver):
    name = "proc"
    description = "Process list and control"
    category = "system"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"count": len(psutil.pids())})

    def status(self) -> Result:
        return self.read(limit=10)

    def read(self, sort: str = "cpu", limit: int = 20,
             user: Optional[str] = None, name: Optional[str] = None, pid: Optional[int] = None, **_) -> Result:
        if pid is not None:
            return self._one(pid)
        # list
        psutil.cpu_percent(interval=None)
        raw = []
        for p in psutil.process_iter(["pid", "name", "username", "status", "ppid", "cmdline"]):
            try:
                info = p.info
                info["cpu"] = p.cpu_percent(interval=0)
                info["mem"] = p.memory_percent()
                raw.append(info)
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                continue
        time.sleep(0.15)
        for p in psutil.process_iter(["pid"]):
            try:
                for info in raw:
                    if info["pid"] == p.pid:
                        info["cpu"] = p.cpu_percent(interval=0)
                        break
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                pass
        if user:
            raw = [x for x in raw if (x.get("username") or "") == user]
        if name:
            nf = name.lower()
            raw = [x for x in raw if nf in (x.get("name") or "").lower()]
        key = "mem" if sort in ("mem", "memory") else "cpu"
        raw.sort(key=lambda x: x.get(key) or 0, reverse=True)
        out = []
        for info in raw[:limit]:
            out.append({
                "pid": info["pid"], "ppid": info.get("ppid"),
                "name": info.get("name"), "user": info.get("username"),
                "cpu": round(info.get("cpu") or 0, 1),
                "mem": round(info.get("mem") or 0, 1),
                "status": info.get("status"),
                "cmdline": " ".join(info.get("cmdline") or [])[:100],
            })
        return _ok(out, total=len(raw), sort=key, limit=limit)

    def _one(self, pid: int) -> Result:
        try:
            p = psutil.Process(pid)
            with p.oneshot():
                mi = p.memory_info()
                return _ok({
                    "pid": p.pid, "ppid": p.ppid(), "name": p.name(),
                    "exe": p.exe() if hasattr(p, "exe") else None,
                    "cmdline": p.cmdline(), "user": p.username(),
                    "status": p.status(),
                    "cpu": p.cpu_percent(interval=0.1),
                    "mem": p.memory_percent(),
                    "mem_rss": mi.rss, "mem_rss_h": _bytes_h(mi.rss),
                    "threads": p.num_threads(), "nice": p.nice(),
                    "create_time": datetime.fromtimestamp(p.create_time()).isoformat(timespec="seconds"),
                    "cwd": p.cwd() if hasattr(p, "cwd") else None,
                })
        except psutil.NoSuchProcess:
            return _err(f"No process PID {pid}")
        except psutil.AccessDenied:
            return _err(f"Access denied for PID {pid}")


class SystemDriver(Driver):
    name = "system"
    description = "Host OS and Skyline identity"
    category = "system"
    requires_caps = {CAP_MONITOR}

    def probe(self) -> Result:
        return _ok({"platform": platform.system()})

    def status(self) -> Result:
        return self.read()

    def read(self, **_) -> Result:
        uname = platform.uname()
        boot = datetime.fromtimestamp(psutil.boot_time())
        uptime = datetime.now() - boot
        skyl_uptime = datetime.now() - self.kernel.boot_time
        return _ok({
            "hostname": socket.gethostname(),
            "os": f"{uname.system} {uname.release}",
            "kernel_host": uname.version,
            "arch": uname.machine,
            "processor": uname.processor or platform.processor() or "N/A",
            "python": platform.python_version(),
            "host_boot": boot.isoformat(timespec="seconds"),
            "host_uptime": str(uptime).split(".")[0],
            "skyline_version": self.kernel.VERSION,
            "skyline_uptime": str(skyl_uptime).split(".")[0],
            "skyline_sessions": len(self.kernel.sessions),
        })


# ===========================================================================
# KERNEL
# ===========================================================================

class SkylineKernel:
    VERSION = "1.1.0"
    NAME = "Skyline"

    def __init__(self):
        self.boot_time = datetime.now()
        self.sessions: Dict[str, Session] = {}
        self.drivers = DriverRegistry(self)
        self._register_builtin_drivers()
        self._default_principal = self._make_principal_from_host()

    def _register_builtin_drivers(self):
        for cls in (
            SystemDriver, CpuDriver, MemDriver, DiskDriver, NetDriver,
            SensorsDriver, BatteryDriver, UsbDriver, PciDriver,
            RoutesDriver, ArpDriver, DnsDriver,
            WifiDriver, BluetoothDriver, ProcessDriver,
        ):
            self.drivers.register(cls(self))

    def _make_principal_from_host(self, role: str = "user") -> Principal:
        try:
            host_user = pwd.getpwuid(os.getuid()).pw_name
            host_uid = os.getuid()
        except Exception:
            host_user, host_uid = "skyline", getattr(os, "getuid", lambda: 0)()
        if host_uid == 0:
            role = "admin"
        return Principal(name=host_user, role=role, host_uid=host_uid, host_user=host_user)

    def new_session(self, name: Optional[str] = None, role: str = "user") -> Session:
        p = self._make_principal_from_host(role=role)
        if name:
            p.name = name
        sess = Session(p)
        self.sessions[p.session_id] = sess
        return sess

    # convenience passthroughs used by older call sites / snapshot
    def snapshot(self) -> Result:
        cpu = self.drivers.get("cpu")
        mem = self.drivers.get("mem")
        disk = self.drivers.get("disk")
        net = self.drivers.get("net")
        c = cpu.read().data if cpu else {}
        m = mem.read().data if mem else {}
        d = disk.read().data if disk else {}
        n = net.read().data if net else {}
        return _ok({
            "ts": datetime.now().isoformat(timespec="seconds"),
            "cpu_percent": c.get("percent"),
            "mem_percent": (m.get("ram") or {}).get("percent"),
            "disk_root_percent": next(
                (p["percent"] for p in (d.get("partitions") or []) if p["mount"] == "/"), None),
            "loadavg": c.get("loadavg"),
            "net_rx": sum(i.get("rx", 0) for i in (n.get("interfaces") or [])),
            "net_tx": sum(i.get("tx", 0) for i in (n.get("interfaces") or [])),
            "skyline": self.VERSION,
            "drivers": len(self.drivers.names()),
        })

    def kill(self, pid: int, sig: str, sess: Session) -> Result:
        deny = sess.principal.require(CAP_PROC_OTHER, CAP_PROC_SELF, CAP_SYS_ADMIN)
        if deny:
            if sess.principal.has(CAP_PROC_SELF):
                try:
                    if psutil.Process(pid).uids().real != os.getuid():
                        return _err(deny)
                except Exception:
                    return _err(deny)
            else:
                return _err(deny)
        sig_map = {
            "TERM": signal.SIGTERM, "KILL": signal.SIGKILL,
            "STOP": signal.SIGSTOP, "CONT": signal.SIGCONT,
            "HUP": signal.SIGHUP, "INT": signal.SIGINT,
            "QUIT": signal.SIGQUIT, "USR1": signal.SIGUSR1, "USR2": signal.SIGUSR2,
        }
        s = sig_map.get(sig.upper())
        if s is None:
            try:
                s = int(sig)
            except ValueError:
                return _err(f"Unknown signal: {sig}")
        try:
            p = psutil.Process(pid)
            name = p.name()
            p.send_signal(s)
            return _ok({"pid": pid, "name": name, "signal": sig.upper()}, action="kill")
        except psutil.NoSuchProcess:
            return _err(f"No process PID {pid}")
        except psutil.AccessDenied:
            return _err(f"Host permission denied for PID {pid}")
        except Exception as e:
            return _err(str(e))

    def renice(self, pid: int, nice: int, sess: Session) -> Result:
        deny = sess.principal.require(CAP_SYS_NICE, CAP_SYS_ADMIN)
        if deny:
            return _err(deny)
        if not -20 <= nice <= 19:
            return _err("nice must be -20..19")
        try:
            p = psutil.Process(pid)
            old = p.nice()
            p.nice(nice)
            return _ok({"pid": pid, "old_nice": old, "new_nice": nice}, action="renice")
        except Exception as e:
            return _err(str(e))

    def set_affinity(self, pid: int, cpus: List[int], sess: Session) -> Result:
        deny = sess.principal.require(CAP_SYS_NICE, CAP_SYS_ADMIN)
        if deny:
            return _err(deny)
        try:
            p = psutil.Process(pid)
            old = p.cpu_affinity()
            p.cpu_affinity(cpus)
            return _ok({"pid": pid, "old": old, "new": cpus}, action="affinity")
        except Exception as e:
            return _err(str(e))

    def net_ping(self, host: str, count: int = 3, timeout: float = 2.0) -> Result:
        code, out, err = _run(
            ["ping", "-c", str(count), "-W", str(int(timeout)), host],
            timeout=timeout * count + 5,
        )
        return _ok({"host": host, "exit": code, "stdout": out, "ok": code == 0})

    def net_resolve(self, host: str) -> Result:
        try:
            infos = socket.getaddrinfo(host, None)
            addrs = sorted({i[4][0] for i in infos})
            return _ok({"host": host, "addresses": addrs})
        except Exception as e:
            return _err(str(e))


# ===========================================================================
# SKL LANGUAGE
# ===========================================================================

@dataclass
class Statement:
    verb: str
    obj: Optional[str] = None
    args: List[str] = field(default_factory=list)
    flags: Dict[str, str] = field(default_factory=dict)
    raw: str = ""
    background: bool = False
    sudo: bool = False


class SKLParser:
    VERBS = {
        "get", "list", "show", "info", "snapshot",
        "kill", "terminate", "forcekill", "suspend", "resume",
        "renice", "affinity",
        "ifup", "ifdown", "ping", "resolve", "routes", "arp", "sockets", "dns",
        "hardware", "usb", "pci", "sensors", "thermal",
        "cd", "pwd", "env", "set", "export", "unset",
        "whoami", "id", "caps", "role", "sessions", "jobs",
        "exec", "run", "system",
        "help", "version", "clear", "history",
        "watch", "login", "su", "echo", "cat", "ls",
        # 1.1
        "drivers", "driver", "wifi", "bluetooth", "bt",
        "sudo", "unsudo",
    }

    ALIASES = {
        "ps": "list", "top": "list",
        "stop": "suspend", "cont": "resume", "continue": "resume",
        "term": "terminate", "sigkill": "forcekill",
        "?": "help", "man": "help", "snap": "snapshot", "ver": "version",
        "bt": "bluetooth",
    }

    OBJECTS = {
        "cpu", "mem", "memory", "disk", "net", "network", "proc", "process",
        "system", "sys", "sensors", "temp", "battery", "bat", "power",
        "hardware", "hw", "usb", "pci", "routes", "arp", "sockets", "dns",
        "thermal", "iface", "interface", "wifi", "bluetooth", "bt",
    }

    def parse_line(self, line: str) -> Optional[Statement]:
        line = line.strip()
        if not line or line.startswith("#"):
            return None
        if "#" in line:
            line = re.sub(r"\s+#.*$", "", line)

        background = False
        if line.endswith("&"):
            background = True
            line = line[:-1].rstrip()

        tokens = self._tokenize(line)
        if not tokens:
            return None

        sudo = False
        if tokens[0].lower() == "sudo":
            sudo = True
            tokens = tokens[1:]
            if not tokens:
                return Statement(verb="sudo", raw=line, sudo=True)
            # bare sudo with only flags:  sudo for=5
            if all(("=" in t and not t.startswith("=")) or t.startswith("-") for t in tokens):
                flags_only: Dict[str, str] = {}
                for t in tokens:
                    if "=" in t and not t.startswith("="):
                        k, _, v = t.partition("=")
                        flags_only[k.lower().lstrip("-")] = v
                    elif t.startswith("--"):
                        flags_only[t[2:].lower()] = "1"
                    elif t.startswith("-") and len(t) > 1:
                        flags_only[t.lstrip("-").lower()] = "1"
                return Statement(verb="sudo", flags=flags_only, raw=line, sudo=True)

        verb = tokens[0].lower()
        verb = self.ALIASES.get(verb, verb)

        obj = None
        args: List[str] = []
        flags: Dict[str, str] = {}
        rest = tokens[1:]

        if rest and "=" not in rest[0] and not rest[0].startswith("-"):
            if rest[0].lower() in self.OBJECTS or verb in ("get", "list", "show", "info", "driver"):
                obj = rest[0].lower()
                obj = {
                    "memory": "mem", "network": "net", "process": "proc",
                    "sys": "system", "temp": "sensors", "bat": "battery",
                    "power": "battery", "iface": "net", "interface": "net",
                    "hw": "hardware", "bt": "bluetooth",
                }.get(obj, obj)
                rest = rest[1:]

        for t in rest:
            if "=" in t and not t.startswith("="):
                k, _, v = t.partition("=")
                flags[k.lower().lstrip("-")] = v
            elif t.startswith("--"):
                flags[t[2:].lower()] = "1"
            elif t.startswith("-") and len(t) > 1 and not t[1].isdigit():
                flags[t.lstrip("-").lower()] = "1"
            else:
                args.append(t)

        return Statement(verb=verb, obj=obj, args=args, flags=flags, raw=line,
                         background=background, sudo=sudo)

    def parse(self, text: str) -> List[Statement]:
        text = text.replace("&&", ";")
        stmts = []
        for part in re.split(r"[;\n]", text):
            s = self.parse_line(part)
            if s:
                stmts.append(s)
        return stmts

    def _tokenize(self, line: str) -> List[str]:
        tokens = []
        current: List[str] = []
        in_quote = False
        quote_char = None
        for ch in line:
            if in_quote:
                if ch == quote_char:
                    in_quote = False
                else:
                    current.append(ch)
            else:
                if ch in ('"', "'"):
                    in_quote = True
                    quote_char = ch
                elif ch.isspace():
                    if current:
                        tokens.append("".join(current))
                        current = []
                else:
                    current.append(ch)
        if current:
            tokens.append("".join(current))
        return tokens


class SKLExecutor:
    def __init__(self, kernel: SkylineKernel, session: Session):
        self.kernel = kernel
        self.session = session
        self.parser = SKLParser()

    def run(self, text: str) -> List[Result]:
        text = self._expand(text)
        results = []
        for stmt in self.parser.parse(text):
            # sudo prefix: temporarily elevate for this statement
            elevated = False
            if stmt.sudo or stmt.verb == "sudo":
                r = self._handle_sudo(stmt)
                if stmt.verb == "sudo" and not stmt.args and not stmt.obj:
                    results.append(r)
                    continue
                if not r.ok:
                    results.append(r)
                    continue
                elevated = True

            r = self.execute(stmt)
            self.session.last_result = r
            results.append(r)

            if elevated and stmt.flags.get("keep") != "1":
                # one-shot sudo unless keep=1
                pass  # grant_sudo already set a timer; leave it
        return results

    def _expand(self, text: str) -> str:
        def repl(m):
            name = m.group(1) or m.group(2)
            return self.session.getvar(name) or ""
        return re.sub(r"\$\{([A-Za-z_][A-Za-z0-9_]*)\}|\$([A-Za-z_][A-Za-z0-9_]*)", repl, text)

    def _handle_sudo(self, stmt: Statement) -> Result:
        p = self.session.principal
        deny = p.require(CAP_SUDO, CAP_SYS_ADMIN, CAP_ALL)
        if deny and os.getuid() != 0:
            return _err(deny)
        minutes = float(stmt.flags.get("for", stmt.flags.get("minutes", "5")))
        p.grant_sudo(minutes=minutes)
        return _ok({
            "sudo": True,
            "until": p.sudo_until.isoformat(timespec="seconds") if p.sudo_until else None,
            "minutes": minutes,
            "role": p.role,
            "effective_caps": sorted(p.effective_caps()),
        }, action="sudo")

    def execute(self, stmt: Statement) -> Result:
        v, o, a, f = stmt.verb, stmt.obj, stmt.args, stmt.flags
        sess = self.session
        k = self.kernel

        try:
            # ---- sudo / unsudo -------------------------------------------
            if v == "sudo":
                return self._handle_sudo(stmt)
            if v == "unsudo":
                sess.principal.drop_sudo()
                return _ok({"sudo": False}, action="unsudo")

            # ---- drivers -------------------------------------------------
            if v == "drivers":
                return _ok(k.drivers.list())
            if v == "driver":
                return self._driver_cmd(o, a, f)

            # ---- wifi / bluetooth high-level -----------------------------
            if v == "wifi":
                return self._wifi_cmd(o, a, f)
            if v in ("bluetooth", "bt"):
                return self._bt_cmd(o, a, f)

            # ---- meta / session ------------------------------------------
            if v == "help":
                return self._help(o or (a[0] if a else None))
            if v == "version":
                return _ok({
                    "name": SkylineKernel.NAME, "version": SkylineKernel.VERSION,
                    "host": platform.platform(), "python": platform.python_version(),
                    "drivers": k.drivers.names(),
                })
            if v in ("whoami", "id"):
                p = sess.principal
                return _ok({
                    "user": p.name, "role": p.role, "session": p.session_id,
                    "host_user": p.host_user,
                    "caps": sorted(p.effective_caps()),
                    "sudo": p.sudo_active(),
                    "sudo_until": p.sudo_until.isoformat(timespec="seconds") if p.sudo_until else None,
                })
            if v == "caps":
                return _ok({
                    "role": sess.principal.role,
                    "capabilities": sorted(sess.principal.effective_caps()),
                    "sudo": sess.principal.sudo_active(),
                })
            if v == "role":
                if a:
                    deny = sess.principal.require(CAP_SESSION, CAP_SYS_ADMIN)
                    if deny:
                        return _err(deny)
                    new_role = a[0]
                    if new_role not in ROLES:
                        return _err(f"Unknown role: {new_role}")
                    sess.principal.role = new_role
                    sess.principal.caps = set(ROLES[new_role])
                    if CAP_ALL in sess.principal.caps:
                        sess.principal.caps = ALL_CAPS.copy()
                    sess.env["SKL_ROLE"] = new_role
                    return _ok({"role": new_role, "caps": sorted(sess.principal.caps)})
                return _ok({"role": sess.principal.role})
            if v == "sessions":
                deny = sess.principal.require(CAP_SESSION, CAP_SYS_ADMIN)
                if deny:
                    return _err(deny)
                return _ok([
                    {"id": s.principal.session_id, "user": s.principal.name,
                     "role": s.principal.role, "cwd": s.cwd}
                    for s in k.sessions.values()
                ])
            if v == "jobs":
                sess.refresh_jobs()
                return _ok([asdict(j) for j in sess.jobs.values()])

            # ---- environment ---------------------------------------------
            if v == "pwd":
                return _ok(sess.cwd)
            if v == "cd":
                target = a[0] if a else sess.env.get("SKL_HOME", str(Path.home()))
                target = os.path.expanduser(target)
                if not os.path.isabs(target):
                    target = os.path.join(sess.cwd, target)
                target = os.path.normpath(target)
                if not os.path.isdir(target):
                    return _err(f"Not a directory: {target}")
                try:
                    os.chdir(target)
                    sess.cwd = target
                    sess.export("PWD", target)
                    return _ok(target)
                except Exception as e:
                    return _err(str(e))
            if v == "env":
                if a:
                    return _ok({a[0]: sess.getvar(a[0])})
                return _ok(dict(sess.env))
            if v in ("set", "export"):
                deny = sess.principal.require(CAP_ENV)
                if deny:
                    return _err(deny)
                if len(a) >= 2:
                    key, val = a[0], a[1]
                elif len(a) == 1 and "=" in a[0]:
                    key, _, val = a[0].partition("=")
                else:
                    return _err("set/export NAME VALUE")
                sess.setvar(key, val)
                if v == "export":
                    sess.export(key, val)
                return _ok({key: val})
            if v == "unset":
                if not a:
                    return _err("unset NAME")
                sess.vars.pop(a[0], None)
                sess.env.pop(a[0], None)
                return _ok({"unset": a[0]})
            if v == "echo":
                return _ok(" ".join(a))
            if v == "history":
                return _ok(sess.history[-50:])
            if v == "ls":
                path = a[0] if a else sess.cwd
                path = os.path.expanduser(path)
                if not os.path.isabs(path):
                    path = os.path.join(sess.cwd, path)
                try:
                    return _ok(sorted(os.listdir(path)), path=path)
                except Exception as e:
                    return _err(str(e))
            if v == "cat":
                if not a:
                    return _err("cat FILE")
                path = a[0] if os.path.isabs(a[0]) else os.path.join(sess.cwd, a[0])
                try:
                    with open(path, "r", errors="replace") as fh:
                        return _ok(fh.read()[:100_000])
                except Exception as e:
                    return _err(str(e))

            # ---- monitor via drivers -------------------------------------
            if v in ("get", "list", "show", "info"):
                return self._get(o, a, f)
            if v == "snapshot":
                return k.snapshot()
            if v in ("hardware", "usb", "pci", "sensors", "thermal", "routes", "arp", "dns"):
                # map short verbs to drivers
                name = {"hardware": "system", "thermal": "sensors"}.get(v, v)
                drv = k.drivers.get(name)
                if not drv:
                    return _err(f"No driver: {name}")
                return drv.read()

            if v == "ping":
                if not a:
                    return _err("ping HOST [count=3]")
                deny = sess.principal.require(CAP_NET_RAW, CAP_MONITOR)
                if deny:
                    return _err(deny)
                return k.net_ping(a[0], count=int(f.get("count", f.get("c", "3"))))
            if v == "resolve":
                if not a:
                    return _err("resolve HOST")
                return k.net_resolve(a[0])
            if v == "sockets":
                try:
                    conns = psutil.net_connections(kind=f.get("kind", "inet"))
                    out = [{
                        "fd": c.fd, "status": c.status, "pid": c.pid,
                        "laddr": f"{c.laddr.ip}:{c.laddr.port}" if c.laddr else None,
                        "raddr": f"{c.raddr.ip}:{c.raddr.port}" if c.raddr else None,
                    } for c in conns]
                    return _ok(out, count=len(out))
                except Exception as e:
                    return _err(str(e))

            # ---- process control -----------------------------------------
            if v == "kill":
                if not a:
                    return _err("kill PID [signal=TERM]")
                sig = f.get("signal") or f.get("sig") or (a[1] if len(a) > 1 else "TERM")
                return k.kill(int(a[0]), sig, sess)
            if v == "terminate":
                return k.kill(int(a[0]), "TERM", sess) if a else _err("PID required")
            if v == "forcekill":
                return k.kill(int(a[0]), "KILL", sess) if a else _err("PID required")
            if v == "suspend":
                return k.kill(int(a[0]), "STOP", sess) if a else _err("PID required")
            if v == "resume":
                return k.kill(int(a[0]), "CONT", sess) if a else _err("PID required")
            if v == "renice":
                if len(a) < 2:
                    return _err("renice PID NICE")
                return k.renice(int(a[0]), int(a[1]), sess)
            if v == "affinity":
                if len(a) < 2:
                    return _err("affinity PID cpu0,cpu1,...")
                return k.set_affinity(int(a[0]), [int(x) for x in a[1].split(",")], sess)

            # ---- net control ---------------------------------------------
            if v in ("ifup", "ifdown"):
                deny = sess.principal.require(CAP_NET_ADMIN, CAP_SYS_ADMIN)
                if deny:
                    return _err(deny)
                name = o or (a[0] if a else None)
                if not name:
                    return _err(f"{v} IFACE")
                drv = k.drivers.get("net")
                return drv.ioctl("up" if v == "ifup" else "down", iface=name)

            # ---- host escape ---------------------------------------------
            if v in ("exec", "run", "system"):
                deny = sess.principal.require(CAP_SYS_ADMIN, CAP_SCRIPT)
                if deny:
                    return _err(deny)
                if not a:
                    return _err("exec COMMAND...")
                cmd = a if v == "exec" else ["bash", "-c", " ".join(a)]
                try:
                    r = subprocess.run(cmd, capture_output=True, text=True, timeout=60, cwd=sess.cwd)
                    return _ok({"exit": r.returncode, "stdout": r.stdout, "stderr": r.stderr}, action="exec")
                except Exception as e:
                    return _err(str(e))

            if v == "watch":
                return _ok({
                    "_watch": True,
                    "targets": o or "cpu,mem",
                    "interval": float(f.get("interval", f.get("i", "1"))),
                }, frontend="watch")

            if v in ("login", "su"):
                role = a[0] if a else "user"
                if role not in ROLES:
                    return _err(f"Unknown role: {role}")
                if role in ("admin", "operator") and not sess.principal.has(CAP_SESSION, CAP_SYS_ADMIN, CAP_ALL):
                    if os.getuid() != 0:
                        return _err("Cannot elevate without session/admin capability or host root")
                sess.principal.role = role
                sess.principal.caps = set(ROLES[role])
                if CAP_ALL in sess.principal.caps:
                    sess.principal.caps = ALL_CAPS.copy()
                sess.env["SKL_ROLE"] = role
                return _ok({"user": sess.principal.name, "role": role, "caps": sorted(sess.principal.caps)})

            return _err(f"Unknown verb: {v}. Try 'help'")

        except ValueError as e:
            return _err(f"Invalid argument: {e}")
        except Exception as e:
            return _err(str(e))

    # ----- driver / wifi / bt helpers -------------------------------------

    def _driver_cmd(self, obj: Optional[str], args: List[str], flags: Dict[str, str]) -> Result:
        k = self.kernel
        if not obj and not args:
            return _ok(k.drivers.list())
        name = obj or args[0]
        drv = k.drivers.get(name)
        if not drv:
            return _err(f"Unknown driver: {name}. Known: {', '.join(k.drivers.names())}")

        # obj = driver name → first arg is action; else args[1] is action
        if obj and args:
            action = args[0]
        elif not obj and len(args) > 1:
            action = args[1]
        else:
            action = flags.get("action", "status")
        if action in ("info", "status", "probe", "read"):
            if action == "info":
                return drv.info()
            if action == "probe":
                return drv.probe()
            if action == "status":
                return drv.status()
            return drv.read(
                detail=flags.get("detail", "0") in ("1", "true", "yes"),
                path=flags.get("path"),
                sort=flags.get("sort", "cpu"),
                limit=int(flags.get("limit", "20")),
            )
        if action == "enable":
            deny = self.session.principal.require(CAP_DRIVER, CAP_SYS_ADMIN)
            if deny:
                return _err(deny)
            return drv.enable()
        if action == "disable":
            deny = self.session.principal.require(CAP_DRIVER, CAP_SYS_ADMIN)
            if deny:
                return _err(deny)
            return drv.disable()
        if action == "ioctl":
            req = flags.get("request") or (args[2] if len(args) > 2 else None)
            if not req:
                return _err("driver NAME ioctl request=...")
            return drv.ioctl(req, **{k2: v for k2, v in flags.items() if k2 != "request"})
        # default: read
        return drv.read(detail=flags.get("detail") in ("1", "true", "yes"))

    def _wifi_cmd(self, obj: Optional[str], args: List[str], flags: Dict[str, str]) -> Result:
        drv = self.kernel.drivers.get("wifi")
        if not drv:
            return _err("wifi driver missing")
        action = obj or (args[0] if args else "status")
        if action in ("status", "list", "info", "read"):
            return drv.read()
        if action == "scan":
            deny = self.session.principal.require(CAP_NET_RAW, CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            return drv.ioctl("scan", iface=flags.get("iface"))
        if action == "connect":
            deny = self.session.principal.require(CAP_NET_ADMIN, CAP_SYS_ADMIN)
            if deny:
                return _err(deny)
            ssid = flags.get("ssid") or (args[1] if len(args) > 1 else (args[0] if args and action != args[0] else None))
            # allow: wifi connect MySSID password=secret
            if not ssid and args:
                ssid = args[0] if action != "connect" else (args[1] if len(args) > 1 else args[0])
            return drv.ioctl("connect", ssid=ssid, password=flags.get("password"), iface=flags.get("iface"))
        if action == "disconnect":
            deny = self.session.principal.require(CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            return drv.ioctl("disconnect", iface=flags.get("iface"))
        if action in ("radio", "on", "off"):
            deny = self.session.principal.require(CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            state = "on" if action == "on" else ("off" if action == "off" else flags.get("state", "on"))
            return drv.ioctl("radio", state=state)
        return drv.read()

    def _bt_cmd(self, obj: Optional[str], args: List[str], flags: Dict[str, str]) -> Result:
        drv = self.kernel.drivers.get("bluetooth")
        if not drv:
            return _err("bluetooth driver missing")
        action = obj or (args[0] if args else "status")
        if action in ("status", "list", "info", "read"):
            return drv.read()
        if action == "scan":
            deny = self.session.principal.require(CAP_NET_RAW, CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            return drv.ioctl("scan", timeout=float(flags.get("timeout", "8")))
        if action == "power":
            deny = self.session.principal.require(CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            return drv.ioctl("power", state=flags.get("state", args[1] if len(args) > 1 else "on"))
        if action in ("pair", "connect", "disconnect"):
            deny = self.session.principal.require(CAP_NET_ADMIN)
            if deny:
                return _err(deny)
            mac = flags.get("mac") or (args[1] if len(args) > 1 else (args[0] if args else None))
            return drv.ioctl(action, mac=mac)
        return drv.read()

    def _get(self, obj: Optional[str], args: List[str], flags: Dict[str, str]) -> Result:
        k = self.kernel
        detail = flags.get("detail", flags.get("d", "0")) in ("1", "true", "yes")
        if not obj:
            return k.snapshot()

        # map object → driver
        mapping = {
            "system": "system", "cpu": "cpu", "mem": "mem", "disk": "disk",
            "net": "net", "proc": "proc", "process": "proc",
            "sensors": "sensors", "battery": "battery", "thermal": "sensors",
            "usb": "usb", "pci": "pci", "routes": "routes", "arp": "arp",
            "dns": "dns", "wifi": "wifi", "bluetooth": "bluetooth",
            "hardware": "system",
        }
        name = mapping.get(obj)
        if name:
            drv = k.drivers.get(name)
            if not drv:
                return _err(f"Driver not loaded: {name}")
            if name == "proc" and args and args[0].isdigit():
                return drv.read(pid=int(args[0]))
            if name == "proc":
                return drv.read(
                    sort=flags.get("sort", flags.get("s", "cpu")),
                    limit=int(flags.get("limit", flags.get("n", "20"))),
                    user=flags.get("user", flags.get("u")),
                    name=flags.get("name") or (args[0] if args and not args[0].isdigit() else None),
                )
            if name == "disk":
                return drv.read(path=args[0] if args else flags.get("path"))
            if name in ("cpu", "net"):
                return drv.read(detail=detail)
            return drv.read()

        if obj.isdigit():
            drv = k.drivers.get("proc")
            return drv.read(pid=int(obj)) if drv else _err("proc driver missing")
        return _err(f"Unknown object: {obj}")

    def _help(self, topic: Optional[str] = None) -> Result:
        text = f"""
{SkylineKernel.NAME} Kernel  v{SkylineKernel.VERSION}
Userspace OS layer on Linux  •  Driver system  •  SKL language

DRIVERS (1.1)
  drivers                     List all drivers + probe status
  driver <name>               Read driver (status)
  driver <name> info|probe|status|read|enable|disable
  driver <name> ioctl request=... key=val

  Built-in drivers:
    system cpu mem disk net sensors battery usb pci
    routes arp dns wifi bluetooth proc

WIFI
  wifi / wifi status          Interfaces & connections
  wifi scan                   Scan access points
  wifi connect SSID [password=...]
  wifi disconnect
  wifi radio on|off

BLUETOOTH
  bluetooth / bt              Adapters & paired devices
  bt scan [timeout=8]
  bt power on|off
  bt pair MAC · bt connect MAC · bt disconnect MAC

SUDO
  sudo                        Elevate capabilities for ~5 minutes
  sudo for=15                 Elevate for 15 minutes
  sudo <command>              Elevate then run command
  unsudo                      Drop elevation
  whoami                      Shows sudo status

IDENTITY
  whoami · caps · role [name] · sessions · jobs · login ROLE

ENVIRONMENT
  pwd · cd · env · set · export · unset · echo · ls · cat · history

MONITOR
  get system|cpu|mem|disk|net|proc|sensors|usb|pci|routes|arp|dns|wifi|bluetooth
  get cpu detail=1 · get proc sort=mem limit=10 · snapshot

NETWORK
  ping HOST · resolve HOST · ifup IFACE · ifdown IFACE · sockets

PROCESS
  kill · terminate · forcekill · suspend · resume · renice · affinity

HOST
  exec · run · watch cpu,mem interval=1 · version · help

Permissions: monitor proc.self proc.other net.admin net.raw
             sys.nice sys.admin session env script driver sudo all
Roles: guest → user → operator → admin
"""
        return _ok(text.strip())


# ===========================================================================
# RENDERER (compact)
# ===========================================================================

class Renderer:
    def __init__(self, fmt: str = "pretty"):
        self.fmt = fmt

    def render(self, result: Result) -> str:
        if self.fmt == "json":
            return result.to_json()
        if not result.ok:
            return f"ERROR: {result.error}"
        if result.data is None:
            return "OK"
        if isinstance(result.data, str):
            return result.data
        if self.fmt == "raw":
            return str(result.data)
        return self._pretty(result)

    def _bar(self, pct: float, w: int = 16) -> str:
        filled = int(w * min(pct, 100) / 100)
        color = "green" if pct < 50 else "yellow" if pct < 80 else "red"
        return f"[{color}]{'█' * filled}{'░' * (w - filled)}[/{color}] {pct:5.1f}%"

    def _pretty(self, result: Result) -> str:
        if not RICH:
            return json.dumps(result.data, indent=2, default=str)
        data = result.data
        if isinstance(data, list) and data and isinstance(data[0], dict) and "category" in data[0] and "name" in data[0]:
            return self._drivers_table(data)
        if isinstance(data, dict) and "percent" in data and "cores_logical" in data:
            return self._kv("CPU", {
                "Usage": self._bar(data["percent"]),
                "Cores": f"{data.get('cores_physical')} phys / {data.get('cores_logical')} logical",
                "Freq": f"{data.get('freq_mhz')} MHz" if data.get("freq_mhz") else "—",
                "Loadavg": "  ".join(f"{x:.2f}" for x in (data.get("loadavg") or [])),
            })
        if isinstance(data, dict) and "ram" in data:
            r, s = data["ram"], data["swap"]
            t = Table(title="Memory", box=box.ROUNDED)
            t.add_column("Type", style="cyan")
            t.add_column("Total")
            t.add_column("Used")
            t.add_column("Avail")
            t.add_column("Usage")
            t.add_row("RAM", r["total_h"], r["used_h"], r["available_h"], self._bar(r["percent"]))
            t.add_row("Swap", s["total_h"], s["used_h"], _bytes_h(s.get("free", 0)),
                      self._bar(s["percent"]) if s["total"] else "—")
            with console.capture() as cap:
                console.print(t)
            return cap.get()
        if isinstance(data, list) and data and isinstance(data[0], dict) and "pid" in data[0]:
            t = Table(title="Processes", box=box.ROUNDED)
            t.add_column("PID", style="cyan", justify="right")
            t.add_column("User")
            t.add_column("Name", max_width=22)
            t.add_column("CPU%", justify="right")
            t.add_column("MEM%", justify="right")
            t.add_column("Status")
            for r in data:
                t.add_row(str(r["pid"]), (r.get("user") or "?")[:10],
                          (r.get("name") or "?")[:22], f"{r['cpu']:.1f}", f"{r['mem']:.1f}",
                          r.get("status") or "")
            with console.capture() as cap:
                console.print(t)
            return cap.get()
        if isinstance(data, dict) and "interfaces" in data and "connections" not in data or (
            isinstance(data, dict) and "interfaces" in data):
            # could be net or wifi
            if data["interfaces"] and isinstance(data["interfaces"][0], dict) and "name" in data["interfaces"][0]:
                t = Table(title="Network", box=box.ROUNDED)
                t.add_column("Iface", style="cyan")
                t.add_column("Up")
                t.add_column("RX")
                t.add_column("TX")
                for i in data["interfaces"]:
                    t.add_row(
                        i.get("name", "?"),
                        "[green]UP[/green]" if i.get("up") else "[red]DOWN[/red]",
                        i.get("rx_h", "—"), i.get("tx_h", "—"),
                    )
                with console.capture() as cap:
                    console.print(t)
                return cap.get()
        if result.meta.get("action"):
            return f"[OK] {result.meta['action']}: {json.dumps(data, default=str)}"
        if isinstance(data, dict):
            return self._kv("Result", {k: v for k, v in data.items() if not isinstance(v, (dict, list)) or k in ("user", "role", "session", "sudo")})
        return json.dumps(data, indent=2, default=str)

    def _kv(self, title: str, d: dict) -> str:
        t = Table(title=title, box=box.ROUNDED, show_header=False)
        t.add_column("Key", style="cyan", width=16)
        t.add_column("Value")
        for k, v in d.items():
            t.add_row(str(k), str(v))
        with console.capture() as cap:
            console.print(t)
        return cap.get()

    def _drivers_table(self, rows: list) -> str:
        t = Table(title="Skyline Drivers", box=box.ROUNDED)
        t.add_column("Name", style="cyan")
        t.add_column("Category")
        t.add_column("Available")
        t.add_column("Enabled")
        t.add_column("Description", max_width=36)
        for r in rows:
            avail = "[green]yes[/green]" if r.get("available") else "[red]no[/red]"
            en = "[green]yes[/green]" if r.get("enabled") else "[dim]no[/dim]"
            t.add_row(r["name"], r.get("category", ""), avail, en, r.get("description", "")[:36])
        with console.capture() as cap:
            console.print(t)
        return cap.get()


# ===========================================================================
# FRONTENDS
# ===========================================================================

HISTORY_FILE = os.path.expanduser("~/.skyline_history")


def run_repl(fmt: str = "pretty", role: str = "user"):
    kernel = SkylineKernel()
    session = kernel.new_session(role=role)
    exe = SKLExecutor(kernel, session)
    renderer = Renderer(fmt)

    banner = f"""
[bold blue]╔════════════════════════════════════════════╗
║       S K Y L I N E   K E R N E L  1.1     ║
║   drivers · wifi · bluetooth · sudo · SKL  ║
╚════════════════════════════════════════════╝[/bold blue]
[dim]user={session.principal.name}  role={session.principal.role}  session={session.principal.session_id}
type [green]help[/green] · [green]drivers[/green] · [green]whoami[/green] · [green]exit[/green][/dim]
"""
    if RICH:
        console.print(banner)
    else:
        print(f"Skyline Kernel v{SkylineKernel.VERSION}  role={session.principal.role}")

    session_ptk = None
    if PTK:
        words = list(SKLParser.VERBS) + list(SKLParser.OBJECTS) + kernel.drivers.names() + [
            "detail=1", "sort=cpu", "sort=mem", "limit=20", "interval=1",
            "count=3", "signal=TERM", "password=", "ssid=", "for=5",
        ]
        style = Style.from_dict({"prompt": "ansicyan bold"})
        session_ptk = PromptSession(
            history=FileHistory(HISTORY_FILE),
            auto_suggest=AutoSuggestFromHistory(),
            completer=WordCompleter(words, ignore_case=True),
            style=style,
        )

    while True:
        try:
            sudo_mark = "sudo:" if session.principal.sudo_active() else ""
            prompt_str = f"skyline:{sudo_mark}{session.principal.role}› "
            if session_ptk:
                line = session_ptk.prompt([("class:prompt", prompt_str)])
            else:
                line = input(prompt_str)
        except (EOFError, KeyboardInterrupt):
            print("\nlogout")
            break

        line = line.strip()
        if not line:
            continue
        if line.lower() in ("exit", "quit", "logout", "q"):
            print("logout")
            break
        if line.lower() == "clear":
            if RICH:
                console.clear()
            else:
                os.system("clear")
            continue

        session.history.append(line)
        stmts = exe.parser.parse(line)
        if stmts and stmts[0].verb == "watch":
            _run_watch(kernel, stmts[0])
            continue

        results = exe.run(line)
        for r in results:
            text = renderer.render(r)
            print(text, end="" if text.endswith("\n") else "\n")


def _run_watch(kernel: SkylineKernel, stmt: Statement):
    targets = (stmt.obj or "cpu,mem").split(",")
    interval = float(stmt.flags.get("interval", stmt.flags.get("i", "1")))
    print(f"watch {targets} every {interval}s  (Ctrl+C stop)")
    try:
        while True:
            bits = []
            for t in targets:
                t = t.strip()
                drv = kernel.drivers.get(t)
                if not drv:
                    continue
                r = drv.status()
                if not r.ok:
                    continue
                d = r.data
                if t == "cpu":
                    bits.append(f"CPU {d.get('percent', 0):5.1f}%")
                elif t == "mem":
                    bits.append(f"MEM {(d.get('ram') or {}).get('percent', 0):5.1f}%")
                elif t == "net":
                    rx = sum(i.get("rx", 0) for i in d.get("interfaces") or [])
                    tx = sum(i.get("tx", 0) for i in d.get("interfaces") or [])
                    bits.append(f"NET ↓{_bytes_h(rx)} ↑{_bytes_h(tx)}")
            print(f"\r[{datetime.now().strftime('%H:%M:%S')}]  " + "  │  ".join(bits) + "   ", end="", flush=True)
            time.sleep(interval)
    except KeyboardInterrupt:
        print("\nstopped")


def run_oneshot(code: str, fmt: str = "json", role: str = "user"):
    kernel = SkylineKernel()
    session = kernel.new_session(role=role)
    exe = SKLExecutor(kernel, session)
    renderer = Renderer(fmt)
    results = exe.run(code)
    for r in results:
        print(renderer.render(r))
        if not r.ok:
            sys.exit(1)


def run_server(host: str = "127.0.0.1", port: int = 7420, role: str = "user"):
    kernel = SkylineKernel()
    srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind((host, port))
    srv.listen(16)
    print(f"Skyline {kernel.VERSION} server {host}:{port}", flush=True)

    def handle(conn: socket.socket, addr):
        session = kernel.new_session(role=role)
        exe = SKLExecutor(kernel, session)
        print(f"+ {addr} session={session.principal.session_id}", flush=True)
        with conn:
            buf = b""
            while True:
                try:
                    chunk = conn.recv(8192)
                except ConnectionResetError:
                    break
                if not chunk:
                    break
                buf += chunk
                while b"\n" in buf:
                    raw, buf = buf.split(b"\n", 1)
                    text = raw.decode("utf-8", errors="replace").strip()
                    if not text:
                        continue
                    if text.lower() in ("quit", "exit", "logout"):
                        conn.sendall(b'{"ok":true,"data":"logout"}\n')
                        return
                    for r in exe.run(text):
                        conn.sendall((r.to_json(indent=None) + "\n").encode())
        print(f"- {addr}", flush=True)

    while True:
        conn, addr = srv.accept()
        threading.Thread(target=handle, args=(conn, addr), daemon=True).start()


def main():
    ap = argparse.ArgumentParser(
        description="Skyline Kernel 1.1 — drivers, wifi, bluetooth, sudo, SKL",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s
  %(prog)s -c "drivers; get cpu; wifi; sudo; whoami"
  %(prog)s -c "driver wifi scan" --json
  %(prog)s --server --port 7420
        """,
    )
    ap.add_argument("-c", "--command", help="Run SKL and exit (- = stdin)")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--raw", action="store_true")
    ap.add_argument("--server", action="store_true")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=7420)
    ap.add_argument("--role", default="user", choices=list(ROLES.keys()))
    args = ap.parse_args()

    fmt = "json" if args.json else ("raw" if args.raw else "pretty")
    if args.server:
        run_server(args.host, args.port, role=args.role)
        return
    if args.command is not None:
        code = sys.stdin.read() if args.command == "-" else args.command
        run_oneshot(code, fmt=fmt, role=args.role)
        return
    run_repl(fmt=fmt, role=args.role)


if __name__ == "__main__":
    main()
