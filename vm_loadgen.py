#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
vm_loadgen.py - 방화벽 세션 부하 생성기 (Palo Alto VM-300 임계치 측정용)

[구성]  노트북(client) ──► Palo Alto VM-300 ──► sink 서버(server)
  * server : 방화벽 반대편 구간에서 실행. 수신 포트 여러 개를 열고 연결을 받아주는 응답기
  * cps    : 초당 신규 세션(CPS) 단계 증가 테스트  (연결 → 요청 → 응답 → 종료)
  * conc   : 동시 세션 단계 증가 테스트           (연결 후 유지 + keepalive)

[빠른 시작]
  # 1) 방화벽 건너편 PC/VM 에서 (포트 100개, 프로세스 2개)
  python vm_loadgen.py server --ports 5001-5100 --procs 2

  # 2) 노트북에서: 초당 세션 생성 1000 → 10000 CPS, 단계당 30초
  python vm_loadgen.py cps  --target 10.10.10.10 --ports 5001-5100 \
         --rate-start 1000 --rate-step 1000 --rate-max 10000 --step-sec 30

  # 3) 노트북에서: 동시 세션 1만 → 30만, 초당 2000개씩 열고 30초 유지
  python vm_loadgen.py conc --target 10.10.10.10 --ports 5001-5100 \
         --sess-step 10000 --sess-max 300000 --open-rate 2000 --hold-sec 30

[판정 방식]  각 단계(stage)가 끝나면 PASS / FAIL / GEN_LIMIT 으로 판정
  PASS       : 실패율, p95 연결지연, 달성률(또는 목표 세션 도달, 세션 유실)이 모두 기준 이내
  FAIL       : 기준 초과 -> 그 직전 PASS 단계가 '안정 구간 최대값', 이 단계가 '임계 초과 지점'
  GEN_LIMIT  : 노트북(생성기) 자원 한계(포트/FD 고갈, 이벤트루프 지연)로 의심 -> 결과 신뢰 불가
              (프로세스 수, 목적지 포트 수, 소스 IP 수를 늘리거나 더 강한 장비 사용)

[주의] 본인이 관리하며 테스트 허가를 받은 장비/구간에서만 사용하세요.
"""

import argparse
import asyncio
import bisect
import csv
import errno
import itertools
import json
import math
import multiprocessing as mp
import os
import re
import signal
import socket
import struct
import subprocess
import sys
import time
from datetime import datetime

# --------------------------------------------------------------------------
# 공통 상수
# --------------------------------------------------------------------------
HTTP_REQ = (b"GET /vm300-loadtest HTTP/1.1\r\nHost: loadtest.local\r\n"
            b"User-Agent: Mozilla/5.0 (loadgen)\r\nAccept: */*\r\n"
            b"Connection: keep-alive\r\n\r\n")
HTTP_RESP = (b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n"
             b"Content-Length: 2\r\nConnection: keep-alive\r\n\r\nOK")
RAW_REQ = b"vm300-loadtest-payload\n"

# 클라이언트 공유 통계 슬롯 (워커 프로세스별 K개, 단일 writer 이므로 lock 불필요)
(S_ATT, S_OK, S_TMO, S_ERR, S_LOCAL, S_DROP,
 S_LATSUM, S_LATCNT, S_EST, S_LAG) = range(10)
HB = 10                                   # 히스토그램 시작 위치
EDGES = [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000]   # ms 상한
NB = len(EDGES) + 1
K = HB + NB

# 로컬(생성기) 자원 고갈로 판단하는 errno (Linux/macOS/Windows)
LOCAL_ERRNOS = {errno.EADDRNOTAVAIL, errno.EMFILE, errno.ENFILE, errno.ENOBUFS,
                errno.ENOMEM, errno.EADDRINUSE, 10048, 10049, 10055, 10024}


# --------------------------------------------------------------------------
# 유틸
# --------------------------------------------------------------------------
def raise_nofile():
    """파일 디스크립터 한도를 가능한 만큼 상향 (Linux/macOS)."""
    try:
        import resource
    except ImportError:
        return None  # Windows
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    cands = [1048576, 262144, 65536, 10240]
    for c in cands:
        want = c if hard == resource.RLIM_INFINITY else min(c, hard)
        try:
            resource.setrlimit(resource.RLIMIT_NOFILE, (want, hard))
            return want
        except (ValueError, OSError):
            continue
    return soft


def parse_ports(spec):
    ports = []
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            lo, hi = part.split("-", 1)
            ports.extend(range(int(lo), int(hi) + 1))
        else:
            ports.append(int(part))
    if not ports:
        raise ValueError("포트 지정이 비어 있습니다")
    return ports


def ephemeral_ports():
    """OS 의 임시(ephemeral) 포트 개수 추정."""
    try:
        if sys.platform.startswith("linux"):
            lo, hi = map(int, open("/proc/sys/net/ipv4/ip_local_port_range").read().split())
            return hi - lo + 1
        if sys.platform == "win32":
            out = subprocess.check_output(
                ["netsh", "int", "ipv4", "show", "dynamicport", "tcp"],
                text=True, errors="ignore")
            nums = []
            for line in out.splitlines():
                if ":" in line:
                    m = re.findall(r"\d+", line.split(":", 1)[1])
                    if m:
                        nums.append(int(m[0]))
            if len(nums) >= 2:
                return nums[1]
        if sys.platform == "darwin":
            lo = int(subprocess.check_output(["sysctl", "-n", "net.inet.ip.portrange.first"]))
            hi = int(subprocess.check_output(["sysctl", "-n", "net.inet.ip.portrange.last"]))
            return hi - lo + 1
    except Exception:
        pass
    return 16384


def classify(e):
    """연결 예외를 통계 슬롯으로 분류."""
    if isinstance(e, (asyncio.TimeoutError, TimeoutError)):
        return S_TMO
    if isinstance(e, OSError) and e.errno in LOCAL_ERRNOS:
        return S_LOCAL
    return S_ERR           # RST/거부/ICMP unreachable 등


def pct_from_hist(hist, p):
    total = sum(hist)
    if total <= 0:
        return 0
    need, c = total * p, 0
    for i, v in enumerate(hist):
        c += v
        if c >= need:
            return EDGES[i] if i < len(EDGES) else EDGES[-1] * 2
    return EDGES[-1] * 2


# --------------------------------------------------------------------------
# SERVER (sink)
# --------------------------------------------------------------------------
class SinkProto(asyncio.Protocol):
    shared = None
    base = 0

    def connection_made(self, transport):
        self.t = transport
        SinkProto.shared[SinkProto.base] += 1          # 누적 accept
        SinkProto.shared[SinkProto.base + 1] += 1      # 현재 연결

    def data_received(self, data):
        self.t.write(HTTP_RESP if data.startswith(b"GET ") else data)

    def connection_lost(self, exc):
        SinkProto.shared[SinkProto.base + 1] -= 1


async def _server_main(bind, ports, backlog):
    loop = asyncio.get_running_loop()
    for p in ports:
        await loop.create_server(SinkProto, bind, p, backlog=backlog)
    await asyncio.Event().wait()


def server_proc(bind, ports, idx, shared, backlog):
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    raise_nofile()
    SinkProto.shared = shared
    SinkProto.base = idx * 2
    try:
        import uvloop
        asyncio.set_event_loop_policy(uvloop.EventLoopPolicy())
    except Exception:
        pass
    asyncio.run(_server_main(bind, ports, backlog))


def cmd_server(a):
    ports = parse_ports(a.ports)
    n = max(1, min(a.procs, len(ports)))
    shared = mp.Array("q", n * 2, lock=False)
    chunks = [ports[i::n] for i in range(n)]
    ps = [mp.Process(target=server_proc, args=(a.bind, chunks[i], i, shared, a.backlog), daemon=True)
          for i in range(n)]
    for p in ps:
        p.start()
    lim = raise_nofile()
    print(f"[server] {a.bind} 포트 {ports[0]}-{ports[-1]} ({len(ports)}개), 프로세스 {n}개, nofile={lim}")
    print("[server] Ctrl+C 로 종료. 1초마다 상태 출력\n")
    prev = 0
    t0 = time.time()
    try:
        while True:
            time.sleep(max(0.0, t0 + int(time.time() - t0) + 1 - time.time()))
            tot = sum(shared[i * 2] for i in range(n))
            cur = sum(shared[i * 2 + 1] for i in range(n))
            print(f"[server] {int(time.time()-t0):6d}s  accept/s={tot-prev:8d}  "
                  f"누적={tot:10d}  현재연결={cur:8d}", flush=True)
            prev = tot
    except KeyboardInterrupt:
        print("\n[server] 종료")


# --------------------------------------------------------------------------
# CLIENT worker
# --------------------------------------------------------------------------
class ClientProto(asyncio.Protocol):
    def __init__(self, fut=None, on_lost=None):
        self.t = None
        self.fut = fut
        self.on_lost = on_lost
        self.closing = False
        self.lost = False
        self.last_rx = time.monotonic()

    def connection_made(self, t):
        self.t = t

    def data_received(self, d):
        self.last_rx = time.monotonic()
        f = self.fut
        if f is not None and not f.done():
            f.set_result(True)

    def connection_lost(self, exc):
        self.lost = True
        f = self.fut
        if f is not None and not f.done():
            f.set_exception(ConnectionResetError("응답 전 연결 종료"))
        if self.on_lost:
            self.on_lost(self)


class Worker:
    def __init__(self, cfg, idx, stats, ctl, stopv):
        self.cfg, self.idx, self.st = cfg, idx, stats
        self.b = idx * K
        self.ctl, self.stopv = ctl, stopv
        combos = [(h, p) for p in cfg.port_list for h in cfg.hosts]
        off = (idx * 7919) % len(combos)
        self.dst = itertools.cycle(combos[off:] + combos[:off])
        self.srcs = itertools.cycle(cfg.src_list) if cfg.src_list else None
        self.sessions = set()
        self.tasks = set()
        self.pending = 0
        self.payload = {"none": None, "raw": RAW_REQ, "http": HTTP_REQ}[cfg.payload]
        self.loop = None

    # ---- 공통 ----
    def observe(self, ms):
        st, b = self.st, self.b
        st[b + S_LATSUM] += ms
        st[b + S_LATCNT] += 1
        st[b + HB + bisect.bisect_left(EDGES, ms)] += 1

    async def connect(self, proto):
        host, port = next(self.dst)
        kw = {}
        if self.srcs:                       # 소스 IP 지정 시에만 bind (포트는 OS 가 선택)
            kw["local_addr"] = (next(self.srcs), 0)
        return await asyncio.wait_for(
            self.loop.create_connection(lambda: proto, host, port, **kw),
            self.cfg.timeout)

    def close_tr(self, tr):
        if self.cfg.close == "rst":
            try:
                tr.get_extra_info("socket").setsockopt(
                    socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
            except Exception:
                pass
            tr.abort()
        else:
            tr.close()

    async def lag_loop(self):
        """이벤트 루프 지연(ms): 생성기 자체가 한계인지 판단하는 지표."""
        while True:
            t = time.perf_counter()
            await asyncio.sleep(0.1)
            lag = (time.perf_counter() - t - 0.1) * 1000.0
            i = self.b + S_LAG
            self.st[i] = max(lag, self.st[i] * 0.9)

    # ---- CPS 모드 ----
    async def cps_session(self):
        st, b = self.st, self.b
        st[b + S_ATT] += 1
        fut = self.loop.create_future() if self.payload else None
        proto = ClientProto(fut)
        t0 = time.perf_counter()
        try:
            tr, _ = await self.connect(proto)
        except Exception as e:
            st[b + classify(e)] += 1
            return
        self.observe((time.perf_counter() - t0) * 1000.0)
        try:
            if self.payload:
                tr.write(self.payload)
                await asyncio.wait_for(fut, self.cfg.timeout)
            st[b + S_OK] += 1
        except Exception as e:
            st[b + classify(e)] += 1
        finally:
            self.close_tr(tr)

    async def run_cps(self):
        last = time.perf_counter()
        carry = 0.0
        cap = max(1, self.cfg.max_inflight // self.cfg.procs)
        while not self.stopv.value:
            await asyncio.sleep(0.005)
            now = time.perf_counter()
            dt, last = now - last, now
            rate = self.ctl.value / self.cfg.procs
            carry += rate * dt
            n = int(carry)
            carry = min(carry - n, rate * 0.2 + 1.0)
            n = min(n, cap - len(self.tasks))
            for _ in range(max(0, n)):
                t = self.loop.create_task(self.cps_session())
                self.tasks.add(t)
                t.add_done_callback(self.tasks.discard)
        for t in list(self.tasks):
            t.cancel()

    # ---- CONC 모드 ----
    def on_lost(self, proto):
        if proto in self.sessions:
            self.sessions.discard(proto)
            self.st[self.b + S_EST] = len(self.sessions)
            if not proto.closing:
                self.st[self.b + S_DROP] += 1

    async def open_hold(self):
        st, b = self.st, self.b
        self.pending += 1
        st[b + S_ATT] += 1
        proto = ClientProto(None, self.on_lost)
        t0 = time.perf_counter()
        try:
            await self.connect(proto)
        except Exception as e:
            st[b + classify(e)] += 1
            return
        finally:
            self.pending -= 1
        self.observe((time.perf_counter() - t0) * 1000.0)
        if proto.lost:
            st[b + S_DROP] += 1
            return
        st[b + S_OK] += 1
        proto.last_rx = time.monotonic()
        self.sessions.add(proto)
        st[b + S_EST] = len(self.sessions)

    async def keepalive_loop(self):
        """주기적으로 데이터를 보내 세션을 살려두고, 응답이 끊긴(유실된) 세션을 집계."""
        ka = self.payload or b"."
        interval = self.cfg.keepalive_sec
        stale_after = interval * 3 + 2
        while True:
            await asyncio.sleep(interval)
            now = time.monotonic()
            for p in list(self.sessions):
                if p.lost:
                    continue
                if now - p.last_rx > stale_after:
                    self.sessions.discard(p)
                    p.closing = True
                    self.st[self.b + S_DROP] += 1
                    p.t.abort()
                else:
                    p.t.write(ka)
            self.st[self.b + S_EST] = len(self.sessions)

    async def run_conc(self):
        last = time.perf_counter()
        carry = 0.0
        rate = self.cfg.open_rate / self.cfg.procs
        pend_cap = max(1, self.cfg.max_pending // self.cfg.procs)
        while not self.stopv.value:
            await asyncio.sleep(0.02)
            now = time.perf_counter()
            dt, last = now - last, now
            tgt = int(self.ctl.value)
            want = tgt // self.cfg.procs + (1 if self.idx < tgt % self.cfg.procs else 0)
            have = len(self.sessions) + self.pending
            if have >= want:
                carry = 0.0
                continue
            carry += rate * dt
            n = int(carry)
            carry = min(carry - n, rate * 0.2 + 1.0)
            n = min(n, want - have, pend_cap - self.pending)
            for _ in range(max(0, n)):
                self.loop.create_task(self.open_hold())

    async def run(self):
        self.loop = asyncio.get_running_loop()
        bg = [self.loop.create_task(self.lag_loop())]
        if self.cfg.cmd == "conc":
            bg.append(self.loop.create_task(self.keepalive_loop()))
            await self.run_conc()
        else:
            await self.run_cps()
        for t in bg:
            t.cancel()
        for p in list(self.sessions):
            p.closing = True
            try:
                p.t.abort()
            except Exception:
                pass
        await asyncio.sleep(0.3)


def worker_entry(cfg, idx, stats, ctl, stopv):
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    raise_nofile()
    try:
        import uvloop
        asyncio.set_event_loop_policy(uvloop.EventLoopPolicy())
    except Exception:
        pass
    asyncio.run(Worker(cfg, idx, stats, ctl, stopv).run())


# --------------------------------------------------------------------------
# CLIENT main (오케스트레이터)
# --------------------------------------------------------------------------
def agg(stats, n):
    tot = [0.0] * K
    for i in range(n):
        b = i * K
        for j in range(K):
            v = stats[b + j]
            if j == S_LAG:
                tot[j] = max(tot[j], v)
            else:
                tot[j] += v
    return tot


def build_plan(a):
    if a.cmd == "cps":
        rmax = a.rate_max or a.rate_start
        rates = list(range(a.rate_start, rmax + 1, a.rate_step)) or [a.rate_start]
        return [{"target": r} for r in rates]
    smax = a.sess_max or a.sess_step
    ts = list(range(a.sess_step, smax + 1, a.sess_step)) or [a.sess_step]
    return [{"target": t} for t in ts]


def evaluate(a, target, base, end, lag_max, dur, reached):
    d = [end[j] - base[j] for j in range(K)]
    att, ok = d[S_ATT], d[S_OK]
    tmo, err, loc = d[S_TMO], d[S_ERR], d[S_LOCAL]
    fails = tmo + err + loc
    fail_pct = (fails / att * 100.0) if att else 0.0
    hist = d[HB:HB + NB]
    p95 = pct_from_hist(hist, 0.95)
    lat_avg = d[S_LATSUM] / d[S_LATCNT] if d[S_LATCNT] else 0.0
    reasons, gen = [], []

    if loc > 0 and att and loc / att > 0.001:
        gen.append(f"로컬 자원 고갈 오류 {int(loc)}건(포트/FD 부족)")
    if lag_max > a.max_lag_ms:
        gen.append(f"생성기 이벤트루프 지연 {lag_max:.0f}ms")

    if fail_pct > a.max_fail_pct:
        reasons.append(f"실패율 {fail_pct:.2f}% > {a.max_fail_pct}% (timeout={int(tmo)}, rst/err={int(err)})")
    if p95 > a.max_p95_ms:
        reasons.append(f"p95 연결지연 {p95}ms > {a.max_p95_ms}ms")
    res = {"target": target, "attempts": int(att), "ok": int(ok), "timeout": int(tmo),
           "rst_err": int(err), "local_err": int(loc), "fail_pct": round(fail_pct, 3),
           "lat_avg_ms": round(lat_avg, 2), "p95_ms": p95, "lag_max_ms": round(lag_max, 1)}
    if a.cmd == "cps":
        achieved = att / dur if dur else 0
        res["achieved_cps"] = round(achieved, 1)
        res["ok_cps"] = round(ok / dur, 1) if dur else 0
        if achieved < target * a.min_achieved_pct / 100.0:
            reasons.append(f"달성 CPS {achieved:.0f} < 목표 {target}의 {a.min_achieved_pct}%")
    else:
        res["established"] = int(end[S_EST])
        res["dropped"] = int(d[S_DROP])
        if not reached:
            reasons.append(f"목표 세션 미도달 ({int(end[S_EST])}/{target})")
        if d[S_DROP] > a.max_drop:
            reasons.append(f"유지 중 세션 유실 {int(d[S_DROP])}건 > {a.max_drop}")
    if gen:
        res["verdict"], res["reasons"] = "GEN_LIMIT", gen + reasons
    elif reasons:
        res["verdict"], res["reasons"] = "FAIL", reasons
    else:
        res["verdict"], res["reasons"] = "PASS", []
    return res


def preflight(a):
    host, port = a.hosts[0], a.port_list[0]
    try:
        s = socket.create_connection((host, port), timeout=a.timeout)
        s.close()
        return True
    except Exception as e:
        print(f"[오류] 사전 연결 확인 실패 {host}:{port} -> {e}")
        print("       sink 서버 실행 여부, 방화벽 보안정책/라우팅/NAT 설정을 확인하세요.")
        return False


def cmd_client(a):
    a.hosts = [socket.gethostbyname(h.strip()) for h in a.target.split(",") if h.strip()]
    a.port_list = parse_ports(a.ports)
    a.src_list = [s.strip() for s in a.src_ips.split(",") if s.strip()] if a.src_ips else []
    a.procs = a.procs or max(1, min(4, (os.cpu_count() or 2) - 1))
    plan = build_plan(a)
    a.out = a.out or f"result_{a.cmd}_{datetime.now():%Y%m%d_%H%M%S}"

    # --- 환경 점검/경고 ---
    lim = raise_nofile()
    eph = ephemeral_ports()
    combos = len(a.hosts) * len(a.port_list) * max(1, len(a.src_list))
    cap = eph * combos
    peak = plan[-1]["target"]
    print("=" * 78)
    print(f" 모드={a.cmd}  대상={','.join(a.hosts)}  포트={a.port_list[0]}-{a.port_list[-1]}({len(a.port_list)}개)"
          f"  워커={a.procs}  payload={a.payload}  close={a.close}")
    print(f" OS ephemeral 포트={eph}, 목적지조합={combos} -> 이론상 동시 연결 상한 약 {cap:,}"
          f"  (nofile={lim if lim else 'N/A'})")
    if a.cmd == "conc" and peak > cap * 0.8:
        print(f" [경고] 목표 최대 세션 {peak:,} 이(가) 상한의 80%를 넘습니다. 포트 수/소스 IP 를 늘리거나 "
              f"ephemeral 범위를 확장하세요.")
    if a.cmd == "cps" and a.close == "fin":
        print(" [참고] close=fin 은 클라이언트 TIME_WAIT 가 쌓입니다. 포트 고갈 시 --close rst 또는 포트 수 증가.")
    print(f" 판정 기준: 실패율<={a.max_fail_pct}%  p95<={a.max_p95_ms}ms  "
          + (f"달성률>={a.min_achieved_pct}%" if a.cmd == "cps" else f"세션유실<={a.max_drop}"))
    print("=" * 78)
    if not preflight(a):
        return 2
    if not a.yes:
        print("본인이 관리/허가받은 장비 구간에서 실행하는 부하 테스트입니다. 방화벽 운영 트래픽에 영향이 없는지 확인했나요?")
        try:
            input("계속하려면 Enter, 취소는 Ctrl+C > ")
        except (KeyboardInterrupt, EOFError):
            print("취소됨")
            return 1

    stats = mp.Array("d", a.procs * K, lock=False)
    ctl = mp.Value("d", 0.0, lock=False)
    stopv = mp.Value("i", 0, lock=False)
    workers = [mp.Process(target=worker_entry, args=(a, i, stats, ctl, stopv)) for i in range(a.procs)]
    for w in workers:
        w.start()

    fcsv = open(a.out + ".csv", "w", newline="", encoding="utf-8-sig")
    cw = csv.writer(fcsv)
    cw.writerow(["elapsed_s", "stage", "target", "attempt", "ok", "timeout", "rst_err", "local_err",
                 "dropped", "established", "lat_avg_ms", "lat_p95_ms", "loop_lag_ms"])
    hdr = (f"{'t(s)':>5} {'stg':>3} {'target':>8} {'att/s':>8} {'ok/s':>8} {'tmo':>6} {'rst/e':>6} "
           f"{'local':>6} {'drop':>6} {'est':>9} {'avg ms':>7} {'p95':>6} {'lag':>5}")
    results = []
    prev = agg(stats, a.procs)
    t_begin = time.time()
    prev_target = 0
    interrupted = False
    try:
        for si, stg in enumerate(plan, 1):
            target = stg["target"]
            ctl.value = target
            base = list(prev)
            lag_max, reached_at, sec = 0.0, None, 0
            ramp_timeout = int(max(1, target - prev_target) / a.open_rate * 2) + 20 if a.cmd == "conc" else 0
            t_stage = time.time()
            print(f"\n--- 단계 {si}/{len(plan)}: 목표 {target:,} "
                  f"{'CPS' if a.cmd == 'cps' else '동시세션'} ---")
            print(hdr)
            while True:
                sec += 1
                time.sleep(max(0.0, t_stage + sec - time.time()))
                cur = agg(stats, a.procs)
                d = [cur[j] - prev[j] for j in range(K)]
                lat = d[S_LATSUM] / d[S_LATCNT] if d[S_LATCNT] else 0.0
                p95 = pct_from_hist(d[HB:HB + NB], 0.95)
                el = int(time.time() - t_begin)
                print(f"{el:5d} {si:3d} {target:8d} {d[S_ATT]:8.0f} {d[S_OK]:8.0f} {d[S_TMO]:6.0f} "
                      f"{d[S_ERR]:6.0f} {d[S_LOCAL]:6.0f} {d[S_DROP]:6.0f} {cur[S_EST]:9.0f} "
                      f"{lat:7.1f} {p95:6d} {cur[S_LAG]:5.0f}", flush=True)
                cw.writerow([el, si, target, int(d[S_ATT]), int(d[S_OK]), int(d[S_TMO]), int(d[S_ERR]),
                             int(d[S_LOCAL]), int(d[S_DROP]), int(cur[S_EST]), round(lat, 2), p95,
                             round(cur[S_LAG], 1)])
                fcsv.flush()
                prev = cur
                lag_max = max(lag_max, cur[S_LAG])
                if a.cmd == "cps":
                    if sec >= a.step_sec:
                        break
                else:
                    if reached_at is None and cur[S_EST] >= target * 0.995:
                        reached_at = sec
                    if reached_at is not None and sec - reached_at >= a.hold_sec:
                        break
                    if sec >= ramp_timeout and reached_at is None:
                        break
            dur = a.step_sec if a.cmd == "cps" else sec
            res = evaluate(a, target, base, prev, lag_max, dur, reached_at is not None)
            res["stage"] = si
            results.append(res)
            tag = {"PASS": "PASS", "FAIL": "FAIL", "GEN_LIMIT": "GEN_LIMIT(생성기 한계 의심)"}[res["verdict"]]
            print(f">>> 단계 {si} 결과: {tag}  실패율={res['fail_pct']}%  p95={res['p95_ms']}ms"
                  + (f"  달성CPS={res['achieved_cps']}" if a.cmd == "cps"
                     else f"  동시세션={res['established']:,}"))
            for r in res["reasons"]:
                print(f"    - {r}")
            prev_target = target
            if res["verdict"] != "PASS" and not a.no_stop:
                print("    (기준 초과로 테스트 중단. 계속하려면 --no-stop)")
                break
    except KeyboardInterrupt:
        interrupted = True
        print("\n[중단] 사용자 인터럽트")
    finally:
        stopv.value = 1
        for w in workers:
            w.join(timeout=15)
            if w.is_alive():
                w.terminate()
        fcsv.close()

    # --- 요약 ---
    print("\n" + "=" * 78)
    print(" 결과 요약")
    print("=" * 78)
    last_pass = None
    first_bad = None
    for r in results:
        if r["verdict"] == "PASS" and first_bad is None:
            last_pass = r
        elif r["verdict"] != "PASS" and first_bad is None:
            first_bad = r
        extra = (f"달성CPS={r['achieved_cps']:>8}  ok_cps={r['ok_cps']:>8}" if a.cmd == "cps"
                 else f"동시세션={r['established']:>9,}  유실={r['dropped']}")
        print(f" 단계{r['stage']:>2} 목표={r['target']:>9,}  {r['verdict']:<9} "
              f"실패율={r['fail_pct']:>6}%  p95={r['p95_ms']:>5}ms  {extra}")
    unit = "CPS" if a.cmd == "cps" else "동시 세션"
    if last_pass:
        print(f"\n ▶ 안정 구간 최대값(마지막 PASS): {last_pass['target']:,} {unit}")
    else:
        print(f"\n ▶ PASS 단계가 없습니다. 시작 부하를 낮추세요.")
    if first_bad:
        print(f" ▶ 최초 기준 초과 지점: {first_bad['target']:,} {unit}  [{first_bad['verdict']}]")
        for r in first_bad["reasons"]:
            print(f"    - {r}")
        if first_bad["verdict"] == "GEN_LIMIT":
            print("    ※ 생성기 한계로 의심되므로 이 값을 방화벽 임계치로 단정하지 마세요.")
    print("\n [방화벽에서 같이 확인할 항목 - 부하 중 별도 SSH 세션에서]")
    print("   show session info                         (활성 세션 수 / 최대 / CPS / 패킷 rate)")
    print("   show running resource-monitor second last 30   (Dataplane CPU, Session 사용량)")
    print("   show system statistics session            (세션 통계)")
    print("   show counter global filter delta yes severity drop   (드롭 카운터)")
    print("   show session packet-buffer-protection / show running resource-monitor ingress-backlogs")
    print(f"\n 산출물: {a.out}.csv , {a.out}.json")
    summary = {
        "mode": a.cmd, "target": a.hosts, "ports": f"{a.port_list[0]}-{a.port_list[-1]}",
        "procs": a.procs, "payload": a.payload, "close": a.close, "interrupted": interrupted,
        "criteria": {"max_fail_pct": a.max_fail_pct, "max_p95_ms": a.max_p95_ms,
                     "max_lag_ms": a.max_lag_ms,
                     "min_achieved_pct": getattr(a, "min_achieved_pct", None),
                     "max_drop": getattr(a, "max_drop", None)},
        "last_pass": last_pass, "first_non_pass": first_bad, "stages": results,
    }
    with open(a.out + ".json", "w", encoding="utf-8") as f:
        json.dump(summary, f, ensure_ascii=False, indent=2)
    return 0


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------
def build_parser():
    p = argparse.ArgumentParser(
        description="방화벽 세션 부하 생성기 (Palo Alto VM-300 임계치 측정용)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("server", help="방화벽 반대편에서 실행하는 sink 서버",
                       formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    s.add_argument("--bind", default="0.0.0.0")
    s.add_argument("--ports", default="5001-5100", help="예: 5001-5100 또는 80,443,8000-8010")
    s.add_argument("--procs", type=int, default=2, help="서버 프로세스 수 (포트를 분배)")
    s.add_argument("--backlog", type=int, default=65535)

    def common(c):
        c.add_argument("--target", required=True, help="sink 서버 IP (쉼표로 여러 개 가능)")
        c.add_argument("--ports", default="5001-5100", help="목적지 포트 범위")
        c.add_argument("--src-ips", default="", help="소스 IP 목록(쉼표). 노트북에 보조 IP를 붙였을 때만 사용")
        c.add_argument("--procs", type=int, default=0, help="워커 프로세스 수 (0=자동)")
        c.add_argument("--timeout", type=float, default=5.0, help="연결/응답 타임아웃(초)")
        c.add_argument("--payload", choices=["http", "raw", "none"], default="http",
                       help="http: HTTP GET (App-ID web-browsing 유도) / raw: 임의 데이터 / none: 핸드셰이크만")
        c.add_argument("--close", choices=["fin", "rst"], default="fin", help="cps 세션 종료 방식")
        c.add_argument("--max-fail-pct", type=float, default=1.0, help="단계 실패율 허용치(%%)")
        c.add_argument("--max-p95-ms", type=int, default=1000, help="p95 연결지연 허용치(ms)")
        c.add_argument("--max-lag-ms", type=float, default=250.0, help="생성기 이벤트루프 지연 한계(ms)")
        c.add_argument("--no-stop", action="store_true", help="기준 초과 후에도 다음 단계 계속")
        c.add_argument("--out", default="", help="결과 파일 접두어(.csv/.json)")
        c.add_argument("--yes", action="store_true", help="실행 전 확인 생략")

    c = sub.add_parser("cps", help="초당 신규 세션(CPS) 단계 증가 테스트",
                       formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    common(c)
    c.add_argument("--rate-start", type=int, default=1000)
    c.add_argument("--rate-step", type=int, default=1000)
    c.add_argument("--rate-max", type=int, default=0, help="0이면 rate-start 한 단계만")
    c.add_argument("--step-sec", type=int, default=30, help="단계 지속 시간(초)")
    c.add_argument("--max-inflight", type=int, default=50000, help="동시 진행중 연결 시도 상한(전체)")
    c.add_argument("--min-achieved-pct", type=float, default=90.0, help="목표 CPS 대비 달성률 하한(%%)")

    n = sub.add_parser("conc", help="동시 세션 단계 증가 테스트",
                       formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    common(n)
    n.add_argument("--sess-step", type=int, default=10000)
    n.add_argument("--sess-max", type=int, default=0, help="0이면 sess-step 한 단계만")
    n.add_argument("--open-rate", type=int, default=2000, help="초당 세션 오픈 속도(전체)")
    n.add_argument("--hold-sec", type=int, default=30, help="목표 도달 후 유지 시간(초)")
    n.add_argument("--keepalive-sec", type=float, default=10.0, help="keepalive 전송/검사 주기(초)")
    n.add_argument("--max-drop", type=int, default=0, help="단계 중 허용 세션 유실 수")
    n.add_argument("--max-pending", type=int, default=5000, help="동시 진행중 오픈 시도 상한(전체)")
    return p


def main():
    a = build_parser().parse_args()
    if a.cmd == "server":
        cmd_server(a)
        return 0
    return cmd_client(a)


if __name__ == "__main__":
    mp.freeze_support()
    sys.exit(main())
