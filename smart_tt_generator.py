#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SMART AI-BASED AUTOMATIC TIMETABLE GENERATOR  (drag-and-drop edition)
=====================================================================

Run:
    python smart_tt_generator_GA.py              -> opens the app; drag & drop the dataset
    python smart_tt_generator_GA.py --dataset X  -> no server; writes Generated_Timetable.html

Nothing about a particular college is hard-coded. Everything is read from the
dataset workbook (sheets: Academic Dataset, Resource Dataset, Batches, Faculty,
Theory Time Slots, Lab Time Slots, Days):

  * semesters, subjects, faculty, theory periods/week, lab sessions/week
  * classrooms / laboratories and which year owns which classroom
  * lab batches, theory + lab time slots, working days

Pipeline
  1. Dataset input + cleaning
  2. Constraint identification
  3. Lab planning      -> Genetic Algorithm places lab blocks, then faculty are paired
  4. Theory planning   -> Genetic Algorithm places every theory period
  5. Independent validation of every hard constraint
  6. Web output inside the EXISTING index.html / styles.css (never edited on disk)
"""

import argparse
import html
import io
import itertools
import json
import math
import random
import re
import threading
import time
import webbrowser
from collections import Counter, defaultdict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote, urlparse, parse_qs

import pandas as pd

BASE_DIR = Path(__file__).resolve().parent
HTML_NAMES = ["mLAC Smart Timetable.html", "index.html", "index(1).html"]
CSS_NAMES = ["styles.css", "styles(1).css"]
SAMPLE_NAMES = ["tt_dataset(1).xlsx", "tt_dataset.xlsx", "tt_dataset(6).xlsx"]
OUTPUT_FILE = BASE_DIR / "Generated_Timetable.html"
PORT = 8765

# ----------------------------------------------------------------------------
# Rules that are policy rather than data
# ----------------------------------------------------------------------------
IGNORED_SUBJECT_WORDS = []   # Do not exclude language or Constitutional Values theory subjects
LANGUAGE_WORDS = ["kannada", "english"]                           # never in labs
# Combined dataset rows that the timetable shows as two separate theory subjects.
SPLIT_SUBJECTS = {"probability & statistics": ("Probability", "Statistics")}
PLACEHOLDER_NAMES = {"", "x", "tba", "tbd", "na", "n/a", "none", "-", "nan"}
# Semesters that also run a Project Lab (semester -> sessions per week). The dataset has no
# Project row, so this rule adds it; a "Project" row in the Academic Dataset overrides it.
PROJECT_LAB_SESSIONS = {5: 2}
HARD = 1000.0                                                     # hard-violation weight

DEFAULT_THEORY = ["8:30-9:20", "9:20-10:10", "10:10-11:00", "11:00-11:50",
                  "11:50-12:40", "12:40-1:30", "1:30-2:20"]
DEFAULT_LAB = ["8:00-11:00", "11:00-2:00", "2:00-5:00"]
DEFAULT_DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]
EMPTY = frozenset()


# ============================================================================
# Small helpers
# ============================================================================
def clean(v):
    if v is None:
        return ""
    if isinstance(v, float) and math.isnan(v):
        return ""
    return re.sub(r"\s+", " ", str(v)).strip()


def fkey(name):
    return re.sub(r"[^a-z0-9]", "", clean(name).lower())


def to_int(v, default=None):
    try:
        s = clean(v)
        if s == "":
            return default
        return int(float(s))
    except (ValueError, TypeError):
        return default


def split_faculty(cell):
    cell = re.sub(r"\band\b", "&", clean(cell), flags=re.I)
    out = []
    for p in re.split(r"[&,/;+]", cell):
        p = p.strip()
        if p.lower() not in PLACEHOLDER_NAMES:
            out.append(p)
    return out


def parse_clock(t):
    h, m = t.split(":")
    h, m = int(h), int(m)
    if 1 <= h <= 6:                       # 1:30 -> 13:30
        h += 12
    return h * 60 + m


def parse_range(s):
    s = clean(s).replace("–", "-").replace("—", "-").replace(" ", "")
    a, b = s.split("-")
    return parse_clock(a), parse_clock(b)


def pretty_range(s):
    return clean(s).replace("-", "–").replace(" ", "")


def ordinal(n):
    if 10 <= n % 100 <= 20:
        suf = "th"
    else:
        suf = {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return f"{n}{suf}"


def find_sheet(sheets, *keys, exclude=()):
    for name, df in sheets.items():
        low = name.lower()
        if all(k in low for k in keys) and not any(x in low for x in exclude):
            return df
    return None


def col(df, *names):
    cols = {str(c).strip().lower(): c for c in df.columns}
    for n in names:                       # exact first
        if n in cols:
            return cols[n]
    for n in names:                       # then substring
        for low, orig in cols.items():
            if n in low:
                return orig
    return None


# ============================================================================
# 1. DATASET -> PROBLEM
# ============================================================================
class TSub:
    """A theory subject (after splitting combined rows)."""
    def __init__(self, sem, name, teachers, periods, source):
        self.sem, self.name, self.teachers = sem, name, teachers
        self.keys = frozenset(fkey(t) for t in teachers)
        self.periods, self.source = periods, source
        self.maxpd = 1


class LSub:
    """A laboratory subject."""
    def __init__(self, sem, name, teachers, sessions, joint):
        self.sem, self.name, self.teachers = sem, name, teachers
        self.keys = [fkey(t) for t in teachers]
        self.sessions, self.joint = sessions, joint

    @property
    def lab_name(self):
        return self.name if self.name.lower().endswith("lab") else f"{self.name} Lab"


class Problem:
    pass


def read_sheets(source, filename="dataset.xlsx"):
    """source: path or bytes."""
    if isinstance(source, (bytes, bytearray)):
        low = filename.lower()
        if low.endswith(".csv"):
            raise ValueError("Please drop the Excel workbook (.xlsx) that contains all the "
                             "dataset sheets - a single CSV cannot hold them.")
        buf = io.BytesIO(source)
        try:
            return pd.read_excel(buf, sheet_name=None)
        except ImportError:
            raise ValueError("This file type needs an extra package. Please save the workbook as .xlsx.")
    return pd.read_excel(source, sheet_name=None)


def load_problem(sheets):
    P = Problem()
    P.notes = []          # data checks shown to the user: (title, text)
    P.flag_rows = 0

    acad = find_sheet(sheets, "academic")
    res = find_sheet(sheets, "resource")
    if acad is None:
        raise ValueError("The workbook has no 'Academic Dataset' sheet.")
    if res is None:
        raise ValueError("The workbook has no 'Resource Dataset' sheet.")
    batch_df = find_sheet(sheets, "batch")
    fac_df = find_sheet(sheets, "faculty", exclude=("academic",))
    th_df = find_sheet(sheets, "theory", "slot")
    lb_df = find_sheet(sheets, "lab", "slot")
    day_df = find_sheet(sheets, "day")

    # ---- days / slots -------------------------------------------------------
    P.days = DEFAULT_DAYS
    if day_df is not None:
        c = col(day_df, "day")
        d = [clean(x) for x in day_df[c].tolist() if clean(x)] if c is not None else []
        if d:
            P.days = d

    def slot_list(df, default):
        if df is None:
            return default
        c = col(df, "time")
        s = [clean(x) for x in df[c].tolist() if clean(x)] if c is not None else []
        return s or default

    P.theory_slots = slot_list(th_df, DEFAULT_THEORY)
    P.lab_slots = slot_list(lb_df, DEFAULT_LAB)
    P.theory_rng = [parse_range(s) for s in P.theory_slots]
    P.lab_rng = [parse_range(s) for s in P.lab_slots]
    # A lab block occupies every theory period it overlaps.
    P.block_slots = []
    for ls, le in P.lab_rng:
        P.block_slots.append(frozenset(i for i, (ts, te) in enumerate(P.theory_rng)
                                       if ts < le and ls < te))

    # ---- resources ----------------------------------------------------------
    c_type, c_name = col(res, "resource type", "type"), col(res, "resource name", "name")
    c_cap, c_use = col(res, "capacity"), col(res, "usage", "note")
    P.classrooms, P.labs, P.room_info = [], [], []
    for _, r in res.iterrows():
        nm, tp = clean(r[c_name]), clean(r[c_type]).lower()
        if not nm:
            continue
        cap = to_int(r[c_cap], 0) if c_cap is not None else 0
        use = clean(r[c_use]) if c_use is not None else ""
        if tp.startswith("lab"):
            P.labs.append(nm)
            P.room_info.append((nm, "Laboratory", cap, use))
        else:
            P.classrooms.append(nm)
            P.room_info.append((nm, "Classroom", cap, use))
    P.room_cap = {n: cap for n, _, cap, _ in P.room_info}
    if not P.classrooms:
        raise ValueError("The Resource Dataset lists no classrooms.")
    if not P.labs:
        P.notes.append(("No laboratories", "The Resource Dataset lists no laboratories, so labs cannot be placed."))

    home, shared = {}, defaultdict(list)
    for nm, tp, cap, use in P.room_info:
        if tp != "Classroom":
            continue
        m = re.search(r"(\d)(?:st|nd|rd|th)\s*year\s*classroom", use, re.I)
        if m:
            home[int(m.group(1)) * 2 - 1] = nm
        m2 = re.search(r"available to (\d)(?:st|nd|rd|th)\s*year", use, re.I)
        if m2:
            shared[int(m2.group(1)) * 2 - 1].append(nm)
    claimed = set(home.values())
    P.home, P.shared = home, shared

    # ---- academic dataset ---------------------------------------------------
    c_sem, c_sub = col(acad, "semester", "sem"), col(acad, "subject")
    c_fac, c_typ = col(acad, "faculty"), col(acad, "subject type", "type")
    c_mark, c_th = col(acad, "marks"), col(acad, "theory periods", "theory")
    c_lreq, c_lses = col(acad, "lab required"), col(acad, "lab sessions")
    c_year = col(acad, "year")
    if None in (c_sem, c_sub, c_fac):
        raise ValueError("Academic Dataset needs Semester, Subject and Faculty columns.")

    P.table_rows, P.theory, P.labsubs = [], defaultdict(list), defaultdict(list)
    P.ignored, P.disp, P.lab_qualified = [], {}, set()
    P.language_keys, P.teaches = set(), defaultdict(list)
    P.n_scheduled_rows = 0

    def remember(name):
        k = fkey(name)
        if k and k not in P.disp:
            P.disp[k] = name
        return k

    for _, r in acad.iterrows():
        subj = clean(r[c_sub])
        sem = to_int(r[c_sem])
        if not subj or sem is None:
            continue
        teachers = split_faculty(r[c_fac])
        for t in teachers:
            remember(t)
        typ = clean(r[c_typ]) if c_typ is not None else ""
        marks = clean(r[c_mark]) if c_mark is not None else "x"
        periods = to_int(r[c_th], 0) if c_th is not None else 0
        lab_req = clean(r[c_lreq]).lower() in {"yes", "y", "true", "1"} if c_lreq is not None else False
        sessions = to_int(r[c_lses], 0) if c_lses is not None else 0
        if lab_req and sessions <= 0:
            sessions = 1
        year = clean(r[c_year]) if c_year is not None else f"{ordinal((sem + 1) // 2)} Year"

        low = subj.lower()
        # Language teachers are identified for LAB exclusion only.
        # Their language theory subjects remain schedulable.
        if any(w in low for w in LANGUAGE_WORDS):
            P.language_keys |= {fkey(t) for t in teachers}
        ignored = False
        flags = []
        P.n_scheduled_rows += 1
        if not teachers:
            flags.append(f"{subj} (Sem {sem}) has no faculty named - it will show as TBA.")
        if marks == "" or marks.lower() in {"na", "n/a", "nan", "-"}:
            flags.append(f"{subj} (Sem {sem}) has no marks value.")
        if flags:
            P.flag_rows += 1
            P.notes.extend((subj, f) for f in flags)

        lab_txt = f"{sessions}/wk" if sessions else "—"
        P.table_rows.append(dict(sem=sem, year=year, subject=subj, faculty=clean(r[c_fac]),
                                 type=typ, marks=marks, theory=periods, lab=lab_txt,
                                 flagged=bool(flags)))
        if ignored:
            continue

        for t in teachers:
            P.teaches[fkey(t)].append((subj, sem))
        if periods > 0:
            if low in SPLIT_SUBJECTS:
                a, b = SPLIT_SUBJECTS[low]
                first = periods - periods // 2
                P.theory[sem].append(TSub(sem, a, teachers, first, subj))
                P.theory[sem].append(TSub(sem, b, teachers, periods // 2, subj))
            else:
                P.theory[sem].append(TSub(sem, subj, teachers, periods, subj))
        if lab_req and sessions > 0:
            joint = typ.strip().lower() == "lab"
            P.labsubs[sem].append(LSub(sem, subj, teachers, sessions, joint))
            for t in teachers:
                P.lab_qualified.add(fkey(t))

    # ---- project lab rule (5th semester: ML + DV + 2 Project = 4 lab blocks) ----
    for sem, n_sessions in PROJECT_LAB_SESSIONS.items():
        subs = P.labsubs.get(sem)
        if not subs or any("project" in x.name.lower() for x in subs):
            continue
        teachers, seen = [], set()
        for x in subs:
            for t in x.teachers:
                if fkey(t) not in seen:
                    seen.add(fkey(t))
                    teachers.append(t)
        P.labsubs[sem].append(LSub(sem, "Project", teachers[:2], n_sessions, True))
        P.notes.append((f"Semester {sem}: Project Lab added",
                        f"{n_sessions} Project Lab blocks per week were added by rule "
                        f"(taught by {' & '.join(teachers[:2])}). Add a 'Project' row to the "
                        "Academic Dataset to change this."))

    # semesters, highest year = highest priority
    P.sems = sorted(set(P.theory) | set(P.labsubs), reverse=True)
    if not P.sems:
        raise ValueError("No schedulable subjects were found in the Academic Dataset.")
    P.theory_sems = [s for s in P.sems if P.theory.get(s)]

    # ---- classroom permissions per semester --------------------------------
    P.rooms_for = {}
    for sem in P.sems:
        lst = []
        if sem in home:
            lst.append(home[sem])
        lst += [r for r in shared.get(sem, []) if r not in lst]
        if not lst:
            lst = [r for r in P.classrooms if r not in claimed] or list(P.classrooms)
            P.notes.append((f"Semester {sem} has no assigned classroom",
                            "Using unassigned classrooms: " + ", ".join(lst)))
        P.rooms_for[sem] = lst

    # ---- batches ------------------------------------------------------------
    P.batches, P.strength = {}, {}
    for sem in P.sems:
        P.batches[sem] = ["Batch A", "Batch B"]
    if batch_df is not None:
        cs = col(batch_df, "semester", "sem")
        cn = col(batch_df, "batch names", "batch name")
        ct = col(batch_df, "total batches", "batches for lab")
        cstr = col(batch_df, "total students", "strength")
        for _, r in batch_df.iterrows():
            sem = to_int(r[cs]) if cs is not None else None
            if sem is None or sem not in P.batches:
                continue
            names = [n.strip() for n in re.split(r"[,&/;]", clean(r[cn])) if n.strip()] if cn is not None else []
            claimed_n = to_int(r[ct]) if ct is not None else None
            if names:
                P.batches[sem] = names
            elif claimed_n:
                P.batches[sem] = [f"Batch {chr(65 + i)}" for i in range(claimed_n)]
            if names and claimed_n and claimed_n != len(names):
                P.notes.append((f"Semester {sem} batch count",
                                f"The sheet says {claimed_n} lab batches but names {len(names)}. "
                                f"Using the {len(names)} named batches."))
                P.flag_rows += 1
            if cstr is not None:
                P.strength[sem] = to_int(r[cstr])
    for sem in P.sems:
        nb = len(P.batches[sem])
        if P.labsubs.get(sem) and nb > len(P.labs):
            P.notes.append((f"Semester {sem} needs {nb} labs at once",
                            f"Only {len(P.labs)} laboratories exist; the extra batches cannot be placed."))
        st = P.strength.get(sem)
        cap = P.room_cap.get(P.rooms_for[sem][0], 0)
        if st and cap and st > cap:
            P.notes.append((f"Semester {sem} classroom capacity",
                            f"{st} students but {P.rooms_for[sem][0]} seats {cap}. "
                            "The timetable follows the room rule; confirm the room is big enough."))
            P.flag_rows += 1

    # ---- faculty sheet: availability + names --------------------------------
    P.unavail = defaultdict(set)
    P.faculty_sheet_keys = set()
    if fac_df is not None:
        cn = col(fac_df, "faculty name", "name")
        ca = col(fac_df, "availability")
        for _, r in fac_df.iterrows():
            nm = clean(r[cn]) if cn is not None else ""
            if nm.lower() in PLACEHOLDER_NAMES:
                continue
            k = remember(nm)
            P.faculty_sheet_keys.add(k)
            txt = clean(r[ca]).lower() if ca is not None else ""
            m = re.search(r"(not available|unavailable|leave|off|except)(.*)", txt)
            if m:
                for di, dn in enumerate(P.days):
                    if dn.lower() in m.group(2) or dn[:3].lower() in re.findall(r"[a-z]+", m.group(2)):
                        P.unavail[k].add(di)
        missing = sorted(P.disp[k] for k in P.teaches if k not in P.faculty_sheet_keys)
        if missing:
            P.notes.append(("Faculty missing from the Faculty sheet",
                            ", ".join(missing) + " teach(es) in the Academic Dataset but have no Faculty-sheet entry."))
            P.flag_rows += 1

    # ---- assistant pool for labs ------------------------------------------
    lang = P.language_keys
    P.pool = sorted(k for k in P.lab_qualified if k not in lang)

    # ---- sanity checks ------------------------------------------------------
    nd, ns = len(P.days), len(P.theory_slots)
    for sem in P.theory_sems:
        tot = sum(s.periods for s in P.theory[sem])
        for s in P.theory[sem]:
            s.maxpd = max(1, math.ceil(s.periods / nd))
            if s.periods > nd:
                P.notes.append((f"{s.name} (Sem {sem})",
                                f"{s.periods} periods/week but only {nd} days; the 'one per day' rule is relaxed."))
        if tot > nd * ns:
            raise ValueError(f"Semester {sem}: {tot} theory periods cannot fit in {nd * ns} weekly slots.")
    # English/Kannada and Constitutional Values are not ignored; they remain theory subjects.
    return P


# ============================================================================
# 2. LAB ROUNDS  (who does which lab, in what rotation)
# ============================================================================
class Round:
    def __init__(self, sem, entries):
        self.sem = sem
        self.entries = entries   # list of dict(batch, sub, base(list of keys), lab_room)
        self.day = self.block = None
        self.base_keys = frozenset(k for e in entries for k in e["base"])


def build_rounds(P):
    rounds = []
    for sem in P.sems:
        subs = P.labsubs.get(sem, [])
        if not subs:
            continue
        batches = P.batches[sem]
        n = len(batches)
        rot = [s for s in subs if not s.joint]
        joint = [s for s in subs if s.joint]

        def mk_joint(s):
            base = [k for k in s.keys if k not in P.language_keys]
            ents = []
            for bi, b in enumerate(batches):
                ents.append(dict(batch=b, sub=s, base=base[bi::n], bi=bi))
            return Round(sem, ents)

        items = []
        for k in range(max([s.sessions for s in rot] or [0])):
            items += [s for s in rot if s.sessions > k]
        m = len(items)
        if m and len({x.name for x in items}) < n:   # too few subjects to rotate -> run together
            for s in items:
                rounds.append(mk_joint(s))
        elif m:
            best = None
            tried = 0
            orders = itertools.permutations(range(m)) if m <= 6 else iter([tuple(range(m))])
            for order in orders:
                tried += 1
                seq = [items[i] for i in order]
                rs, ok = [], True
                for r in range(m):
                    ents, seen = [], set()
                    for bi, b in enumerate(batches):
                        s = seq[(r + bi) % m]
                        base = [k for k in s.keys if k not in P.language_keys][:2]
                        if seen & set(base):
                            ok = False
                        seen |= set(base)
                        ents.append(dict(batch=b, sub=s, base=base, bi=bi))
                    rs.append(Round(sem, ents))
                if ok:
                    best = rs
                    break
                if tried > 800:
                    break
            if best is None:                  # no clash-free pairing exists -> run each together
                best = [mk_joint(x) for x in items]
            rounds += best
        for s in joint:
            for _ in range(s.sessions):
                rounds.append(mk_joint(s))
    return rounds


# ============================================================================
# 3. GA - LAB PLACEMENT
# ============================================================================
class LabPlacer:
    def __init__(self, P, rounds, rng):
        self.P, self.rounds, self.rng = P, rounds, rng
        self.nd, self.nb = len(P.days), len(P.lab_slots)
        self.cells = [(d, b) for d in range(self.nd) for b in range(self.nb)]
        self.cap = max(1, len(P.labs))
        self.ns = len(P.theory_slots)
        self.need = {}
        for sem in P.theory_sems:
            subs = P.theory[sem]
            self.need[sem] = (sum(s.periods for s in subs), sum(s.maxpd for s in subs))

    def cost(self, genes):
        P, hard, soft = self.P, 0, 0.0
        cells = defaultdict(list)
        sem_days = defaultdict(list)
        sem_blocks = defaultdict(dict)
        for r, (d, b) in zip(self.rounds, genes):
            cells[(d, b)].append(r)
            sem_days[r.sem].append(d)
            sem_blocks[r.sem][d] = b
            if any(d in P.unavail.get(k, EMPTY) for k in r.base_keys):
                hard += 1
        for cell, rs in cells.items():
            tot = sum(len(r.entries) for r in rs)
            if tot > self.cap:
                hard += tot - self.cap
            seen = set()
            for r in rs:
                if seen & r.base_keys:
                    hard += 1
                seen |= r.base_keys
        per_day, per_block = Counter(), Counter()
        for sem, ds in sem_days.items():
            c = Counter(ds)
            hard += sum(v - 1 for v in c.values() if v > 1)
            u = sorted(c)
            soft += 2 * sum(1 for a, b in zip(u, u[1:]) if b - a == 1)
            for d in u:
                per_day[d] += 1
            for d, b in sem_blocks[sem].items():
                per_block[b] += 1
            if sem in self.need:
                total, per_day_cap = self.need[sem]
                capacity = 0
                for d in range(self.nd):
                    blk = P.block_slots[sem_blocks[sem][d]] if d in sem_blocks[sem] else EMPTY
                    capacity += min(per_day_cap, self.ns - len(blk))
                if capacity < total:
                    hard += total - capacity
        soft += sum(v * v for v in per_day.values()) + 0.5 * sum(v * v for v in per_block.values())
        return hard * HARD + soft

    def run(self, pop_size=80, gens=220):
        rng, cells, n = self.rng, self.cells, len(self.rounds)
        if n == 0:
            return []
        pop = [[rng.choice(cells) for _ in range(n)] for _ in range(pop_size)]
        scored = [(self.cost(g), g) for g in pop]
        best, stale = min(scored, key=lambda x: x[0]), 0
        for _ in range(gens):
            scored.sort(key=lambda x: x[0])
            nxt = [g[:] for _, g in scored[:6]]
            while len(nxt) < pop_size:
                a = min(rng.sample(scored, 3), key=lambda x: x[0])[1]
                b = min(rng.sample(scored, 3), key=lambda x: x[0])[1]
                cut = rng.randrange(1, n) if n > 1 else 0
                child = a[:cut] + b[cut:]
                if rng.random() < 0.5:
                    child[rng.randrange(n)] = rng.choice(cells)
                if rng.random() < 0.2 and n > 1:
                    i, j = rng.sample(range(n), 2)
                    child[i], child[j] = child[j], child[i]
                nxt.append(child)
            scored = [(self.cost(g), g) for g in nxt]
            cur = min(scored, key=lambda x: x[0])
            if cur[0] < best[0]:
                best, stale = cur, 0
            else:
                stale += 1
            if best[0] < HARD and stale > 40:
                break
        return best[1]


def assign_lab_faculty(P, rounds):
    """Exactly two faculty per batch lab: subject teacher(s) + a lab-qualified CS teacher."""
    load = Counter()
    for sem in P.theory_sems:
        for s in P.theory[sem]:
            for k in s.keys:
                load[k] += s.periods
    sticky = {}
    busy_cell = defaultdict(set)
    for rd in sorted(rounds, key=lambda r: (r.day, r.block, -r.sem)):
        busy = busy_cell[(rd.day, rd.block)]
        reserved = set(rd.base_keys)        # every subject teacher of this block is spoken for
        for e in rd.entries:
            team = list(e["base"])[:2]
            e["lab_room"] = P.labs[e["bi"] % len(P.labs)] if P.labs else "Lab"
            while len(team) < 2:
                sub = e["sub"]
                taken = set(team) | busy | reserved
                cands = [k for k in P.pool
                         if k not in taken and rd.day not in P.unavail.get(k, EMPTY)]
                if not cands:
                    break
                st = sticky.get((rd.sem, sub.name))
                pick = st if st in cands else min(cands, key=lambda k: (load[k], P.disp.get(k, k)))
                sticky[(rd.sem, sub.name)] = pick
                load[pick] += 3
                team.append(pick)
            busy.update(team)
            e["team"] = team
    lab_busy = defaultdict(set)
    for rd in rounds:
        keys = {k for e in rd.entries for k in e["team"]}
        for sl in P.block_slots[rd.block]:
            lab_busy[(rd.day, sl)] |= keys
    return {k: frozenset(v) for k, v in lab_busy.items()}


# ============================================================================
# 4. GA - THEORY PLACEMENT
# ============================================================================
class TheoryGA:
    """
    Chromosome : ind[sem][subject_index] = [(day, slot), ...]   (one entry per weekly period)
    Hard       : slot clash inside a semester, theory inside own lab, same subject twice a day,
                 faculty clash (theory+theory, theory+lab), faculty unavailable, no free room
    Soft       : gaps inside a day, needlessly late starts, uneven daily load (lab days lighter), subjects on
                 consecutive days
    Fitness    : 1 / (1 + conflict score)
    """
    def __init__(self, P, rounds, lab_busy, rng):
        self.P, self.rng, self.lab_busy = P, rng, lab_busy
        self.nd, self.ns = len(P.days), len(P.theory_slots)
        self.sems = P.theory_sems
        self.blocked = {s: [set() for _ in range(self.nd)] for s in self.sems}
        for r in rounds:
            if r.sem in self.blocked:
                self.blocked[r.sem][r.day] |= P.block_slots[r.block]
        self.free = {s: [[x for x in range(self.ns) if x not in self.blocked[s][d]]
                         for d in range(self.nd)] for s in self.sems}
        self.subs = {s: P.theory[s] for s in self.sems}
        self.targets = {}
        for s in self.sems:
            tot = sum(x.periods for x in self.subs[s])
            w = [0.6 if self.blocked[s][d] else 1.0 for d in range(self.nd)]
            tw = sum(w)
            self.targets[s] = [tot * x / tw for x in w]
        self.place = [(s, ti, i) for s in self.sems for ti, sub in enumerate(self.subs[s])
                      for i in range(sub.periods)]

    # ---- construction -----------------------------------------------------
    def random_ind(self):
        rng, ind = self.rng, {}
        for s in self.sems:
            used = set()
            ind[s] = [None] * len(self.subs[s])
            order = sorted(range(len(self.subs[s])), key=lambda i: (-self.subs[s][i].periods, rng.random()))
            for ti in order:
                sub, pl, cnt = self.subs[s][ti], [], Counter()
                days = list(range(self.nd))
                rng.shuffle(days)
                for _ in range(sub.periods):
                    cand = [d for d in days if cnt[d] < sub.maxpd and
                            any((d, x) not in used for x in self.free[s][d])]
                    if not cand:
                        cand = days
                    d = cand[0] if len(cand) == 1 else rng.choice(cand)
                    opts = [x for x in self.free[s][d] if (d, x) not in used] or list(range(self.ns))
                    sl = rng.choice(opts)
                    used.add((d, sl))
                    cnt[d] += 1
                    pl.append((d, sl))
                ind[s][ti] = pl
        return ind

    # ---- fitness ----------------------------------------------------------
    def evaluate(self, ind, rec=None):
        P, hard, soft, bad = self.P, 0, 0.0, []
        fac_used, room_used = {}, {}
        unavail, lab_busy = P.unavail, self.lab_busy
        for s in self.sems:                               # high priority first
            taken, per_day = set(), defaultdict(list)
            blocked = self.blocked[s]
            rooms = P.rooms_for[s]
            for ti, sub in enumerate(self.subs[s]):
                cnt = Counter()
                keys = sub.keys
                for i, (d, sl) in enumerate(ind[s][ti]):
                    ref = (s, ti, i)
                    if (d, sl) in taken:
                        hard += 1
                        bad.append(ref)
                    taken.add((d, sl))
                    if sl in blocked[d]:
                        hard += 1
                        bad.append(ref)
                    cnt[d] += 1
                    if cnt[d] > sub.maxpd:
                        hard += 1
                        bad.append(ref)
                    per_day[d].append(sl)
                    if keys:
                        fu = fac_used.get((d, sl))
                        if fu is None:
                            fu = fac_used[(d, sl)] = set()
                        if (fu & keys) or (keys & lab_busy.get((d, sl), EMPTY)):
                            hard += 1
                            bad.append(ref)
                        if unavail and any(d in unavail.get(k, EMPTY) for k in keys):
                            hard += 1
                            bad.append(ref)
                        fu |= keys
                    ru = room_used.get((d, sl))
                    if ru is None:
                        ru = room_used[(d, sl)] = set()
                    chosen = None
                    for rm in rooms:
                        if rm not in ru:
                            chosen = rm
                            break
                    if chosen is None:
                        hard += 1
                        bad.append(ref)
                    else:
                        ru.add(chosen)
                        if rec is not None:
                            rec[ref] = chosen
            # soft terms
            tg = self.targets[s]
            for d in range(self.nd):
                sl_list = per_day.get(d, [])
                soft += 2.0 * (len(sl_list) - tg[d]) ** 2
                if sl_list:
                    lo, hi = min(sl_list), max(sl_list)
                    occ = set(sl_list) | blocked[d]
                    soft += 4.0 * sum(1 for x in range(lo, hi + 1) if x not in occ)
                    soft += 0.6 * lo          # mild tie-breaker: avoid needlessly late starts
            for ti, sub in enumerate(self.subs[s]):
                ds = sorted({d for d, _ in ind[s][ti]})
                soft += 1.5 * sum(1 for a, b in zip(ds, ds[1:]) if b - a == 1)
        return hard, soft, bad

    # ---- operators --------------------------------------------------------
    def mutate(self, ind, bad):
        rng = self.rng
        child = {s: [list(p) for p in ind[s]] for s in self.sems}
        for _ in range(1 + (rng.random() < 0.5)):
            ref = rng.choice(bad) if bad and rng.random() < 0.75 else rng.choice(self.place)
            s, ti, i = ref
            sub = self.subs[s][ti]
            pls = child[s][ti]
            if rng.random() < 0.65:                       # move
                used = {x for p in child[s] for x in p}
                have = {d for k, (d, _) in enumerate(pls) if k != i}
                days = [d for d in range(self.nd) if d not in have] or list(range(self.nd))
                d = rng.choice(days)
                opts = [x for x in self.free[s][d] if (d, x) not in used] or self.free[s][d] or list(range(self.ns))
                pls[i] = (d, rng.choice(opts))
            else:                                         # swap two periods of the semester
                ti2 = rng.randrange(len(self.subs[s]))
                j = rng.randrange(len(child[s][ti2]))
                pls[i], child[s][ti2][j] = child[s][ti2][j], pls[i]
        return child

    def crossover(self, a, b):
        rng, child = self.rng, {}
        for s in self.sems:
            if rng.random() < 0.3:                        # mix subject by subject
                child[s] = [list(a[s][ti] if rng.random() < 0.5 else b[s][ti])
                            for ti in range(len(self.subs[s]))]
            else:
                src = a if rng.random() < 0.5 else b
                child[s] = [list(p) for p in src[s]]
        return child

    def run(self, pop_size=120, max_gens=700, time_cap=25.0, patience=70):
        rng, t0 = self.rng, time.time()
        pop = []
        for _ in range(pop_size):
            ind = self.random_ind()
            h, sft, bad = self.evaluate(ind)
            pop.append((h * HARD + sft, h, sft, bad, ind))
        best, stale, gen = min(pop, key=lambda x: x[0]), 0, 0
        for gen in range(1, max_gens + 1):
            pop.sort(key=lambda x: x[0])
            nxt = pop[:8]
            while len(nxt) < pop_size:
                a = min(rng.sample(pop, 4), key=lambda x: x[0])
                b = min(rng.sample(pop, 4), key=lambda x: x[0])
                child = self.crossover(a[4], b[4]) if rng.random() < 0.85 else \
                    {s: [list(p) for p in a[4][s]] for s in self.sems}
                child = self.mutate(child, a[3] if rng.random() < 0.5 else b[3])
                h, sft, bad = self.evaluate(child)
                nxt.append((h * HARD + sft, h, sft, bad, child))
            pop = nxt
            cur = min(pop, key=lambda x: x[0])
            if cur[0] < best[0] - 1e-9:
                best, stale = cur, 0
            else:
                stale += 1
            if best[1] == 0 and stale >= patience:
                break
            if time.time() - t0 > time_cap and best[1] == 0:
                break
            if time.time() - t0 > time_cap * 2:
                break
        return best[4], dict(generations=gen, hard=best[1], soft=round(best[2], 1),
                             fitness=1.0 / (1.0 + best[0]), seconds=round(time.time() - t0, 1))

    def build(self, ind):
        rec = {}
        self.evaluate(ind, rec)
        table = {s: [[None] * self.ns for _ in range(self.nd)] for s in self.sems}
        for s in self.sems:
            for ti, sub in enumerate(self.subs[s]):
                for i, (d, sl) in enumerate(ind[s][ti]):
                    table[s][d][sl] = dict(
                        subject=sub.name,
                        faculty=" & ".join(sub.teachers) if sub.teachers else "TBA",
                        room=rec.get((s, ti, i), "?"), sub=sub)
        return table


# ============================================================================
# 5. INDEPENDENT VALIDATION
# ============================================================================
def validate(P, theory, rounds):
    """Re-checks the finished timetable from scratch. Returns [(check, passed, detail)]."""
    nd, ns = len(P.days), len(P.theory_slots)
    out = []

    def add(name, errs):
        out.append((name, not errs, "; ".join(errs[:3]) + (" ..." if len(errs) > 3 else "")))

    # weekly counts
    errs = []
    for s in P.theory_sems:
        cnt = Counter(e["subject"] for d in range(nd) for e in theory[s][d] if e)
        for sub in P.theory[s]:
            if cnt[sub.name] != sub.periods:
                errs.append(f"Sem {s} {sub.name}: {cnt[sub.name]} of {sub.periods}")
    add("Weekly theory periods match the dataset", errs)

    # repeat per day
    errs = []
    for s in P.theory_sems:
        for d in range(nd):
            c = Counter(e["subject"] for e in theory[s][d] if e)
            for sub in P.theory[s]:
                if c[sub.name] > sub.maxpd:
                    errs.append(f"Sem {s} {sub.name} repeats on {P.days[d]}")
    add("No subject repeated on the same day", errs)

    # own lab overlap
    errs = []
    for r in rounds:
        for sl in P.block_slots[r.block]:
            if r.sem in theory and theory[r.sem][r.day][sl]:
                errs.append(f"Sem {r.sem} theory during its lab on {P.days[r.day]}")
    add("No theory during the semester's own lab", errs)

    # faculty clashes: theory+theory (same period), lab+lab (same block), theory+lab (overlap)
    occ = defaultdict(list)                      # (day, period) -> teacher keys in theory
    for s in P.theory_sems:
        for d in range(nd):
            for sl in range(ns):
                e = theory[s][d][sl]
                if e:
                    occ[(d, sl)].extend(e["sub"].keys)
    lab_cell = defaultdict(list)                 # (day, block) -> teacher keys in labs
    for r in rounds:
        for e in r.entries:
            lab_cell[(r.day, r.block)].extend(e["team"])
    errs = []
    for (d, sl), lst in occ.items():
        for k, n in Counter(lst).items():
            if n > 1:
                errs.append(f"{P.disp.get(k, k)} double-booked {P.days[d]} {P.theory_slots[sl]}")
    for (d, b), lst in lab_cell.items():
        for k, n in Counter(lst).items():
            if n > 1:
                errs.append(f"{P.disp.get(k, k)} double-booked in labs {P.days[d]} {P.lab_slots[b]}")
        for sl in P.block_slots[b]:
            for k in set(lst) & set(occ.get((d, sl), [])):
                errs.append(f"{P.disp.get(k, k)} in a lab and a class {P.days[d]} {P.theory_slots[sl]}")
    add("No faculty clash (theory or lab)", errs)

    # unavailable
    errs = []
    for (d, sl), lst in occ.items():
        for k in lst:
            if d in P.unavail.get(k, EMPTY):
                errs.append(f"{P.disp.get(k, k)} unavailable {P.days[d]}")
    for (d, b), lst in lab_cell.items():
        for k in lst:
            if d in P.unavail.get(k, EMPTY):
                errs.append(f"{P.disp.get(k, k)} unavailable {P.days[d]} (lab)")
    add("Faculty availability respected", errs)

    # rooms
    errs, errs2 = [], []
    for d in range(nd):
        for sl in range(ns):
            seen = set()
            for s in P.theory_sems:
                e = theory[s][d][sl]
                if not e:
                    continue
                if e["room"] in seen or e["room"] == "?":
                    errs.append(f"Room clash {e['room']} {P.days[d]} {P.theory_slots[sl]}")
                seen.add(e["room"])
                if e["room"] not in P.rooms_for[s]:
                    errs2.append(f"Sem {s} in {e['room']}")
    add("No classroom clash", errs)
    add("Only permitted classrooms used", errs2)

    # labs
    errs = []
    cells = defaultdict(list)
    for r in rounds:
        cells[(r.day, r.block)].append(r)
        used = [e["lab_room"] for e in r.entries]
        if len(set(used)) != len(used):
            errs.append(f"Lab room reused inside Sem {r.sem} block")
    for (d, b), rs in cells.items():
        used = [e["lab_room"] for r in rs for e in r.entries]
        if len(used) != len(set(used)):
            errs.append(f"Laboratory clash {P.days[d]} {P.lab_slots[b]}")
    add("No laboratory clash", errs)

    errs = []
    per = defaultdict(Counter)
    for r in rounds:
        per[r.sem][r.day] += 1
    for s, c in per.items():
        for d, n in c.items():
            if n > 1:
                errs.append(f"Sem {s} has {n} lab blocks on {P.days[d]}")
    add("At most one lab block per semester per day", errs)

    errs = []
    done = defaultdict(Counter)
    for r in rounds:
        for e in r.entries:
            done[(r.sem, e["batch"])][e["sub"].name] += 1
    for s in P.sems:
        for sub in P.labsubs.get(s, []):
            for b in P.batches[s]:
                if done[(s, b)][sub.name] != sub.sessions:
                    errs.append(f"Sem {s} {b} {sub.name}: {done[(s, b)][sub.name]} of {sub.sessions}")
    add("Every batch gets every required lab session", errs)

    errs = []
    for r in rounds:
        for e in r.entries:
            if len(e["team"]) != 2:
                errs.append(f"Sem {r.sem} {e['sub'].name} {e['batch']} has {len(e['team'])} faculty")
    add("Exactly two faculty per lab", errs)

    errs = []
    for r in rounds:
        for e in r.entries:
            for k in e["team"]:
                if k in P.language_keys and k not in e["base"]:
                    errs.append(f"Language faculty {P.disp.get(k, k)} in a lab")
    add("Language faculty never assigned to labs", errs)
    return out


# ============================================================================
# 6. SOLVE
# ============================================================================
def solve(P, seed=42, attempts=6, log=print):
    t0 = time.time()
    last = None
    for attempt in range(attempts):
        rng = random.Random(seed + attempt * 977)
        rounds = build_rounds(P)
        placer = LabPlacer(P, rounds, rng)
        genes = placer.run()
        for r, (d, b) in zip(rounds, genes):
            r.day, r.block = d, b
        lab_busy = assign_lab_faculty(P, rounds)
        ga = TheoryGA(P, rounds, lab_busy, rng)
        ind, info = ga.run() if P.theory_sems else ({}, dict(generations=0, hard=0, soft=0, fitness=1, seconds=0))
        theory = ga.build(ind) if P.theory_sems else {}
        checks = validate(P, theory, rounds)
        failed = sum(1 for _, ok, _ in checks if not ok)
        log(f"  attempt {attempt + 1}: GA generations={info['generations']}, "
            f"hard conflicts={info['hard']}, validation failures={failed}")
        last = dict(rounds=rounds, theory=theory, checks=checks, info=info, attempt=attempt + 1)
        if failed == 0:
            break
    last["seconds"] = round(time.time() - t0, 1)
    last["passed"] = sum(1 for _, ok, _ in last["checks"] if ok)
    last["failed"] = len(last["checks"]) - last["passed"]
    return last


# ============================================================================
# 7. HTML FRAGMENTS (existing classes only - no CSS is added or changed)
# ============================================================================
def esc(v):
    return html.escape(str(v), quote=True)


def theory_card(e):
    if not e:
        return '<span class="slot-chip free">—</span>'
    return ('<span class="slot-chip theory">' + esc(e["subject"]) +
            f'<em>{esc(e["room"])} · {esc(e["faculty"])}</em></span>')


def lab_cards(P, r):
    out = []
    for e in r.entries:
        team = " & ".join(P.disp.get(k, k) for k in e["team"])
        out.append('<span class="slot-chip lab">' + esc(e["sub"].lab_name) +
                   f'<em>{esc(e["batch"])} · {esc(e["lab_room"])} · {esc(team)}</em>'
                   f'<small>{esc(pretty_range(P.lab_slots[r.block]))}</small></span>')
    return "".join(out)


def sem_table(P, res, sem):
    theory, rounds = res["theory"], res["rounds"]

    # Interleave lab blocks with theory periods by their real start times.
    events = []
    for sl, slot in enumerate(P.theory_slots):
        st, en = P.theory_rng[sl]
        events.append((st, 1, "theory", sl, slot))
    for bi, slot in enumerate(P.lab_slots):
        st, en = P.lab_rng[bi]
        events.append((st, 0, "lab", bi, slot))
    events.sort(key=lambda x: (x[0], x[1]))

    rows = []
    for d, dn in enumerate(P.days):
        cells = [f'<td class="tt-time">{esc(dn)}</td>']
        for _, _, kind, idx, slot in events:
            if kind == "lab":
                matching = [rr for rr in rounds
                            if rr.sem == sem and rr.day == d and rr.block == idx]
                chips = "".join(lab_cards(P, rr) for rr in matching)
                if not chips:
                    chips = '<span class="slot-chip free">—</span>'
                cells.append(f"<td>{chips}</td>")
            else:
                e = theory[sem][d][idx] if sem in theory else None
                cells.append(f"<td>{theory_card(e)}</td>")
        rows.append("<tr>" + "".join(cells) + "</tr>")

    head = ['<th class="tt-time">Day</th>'] + [
        f"<th>{esc(pretty_range(slot))}</th>" for _, _, _, _, slot in events
    ]
    return (f'<div class="grid-wrap sem-grid" id="sem{sem}"><table class="tt-grid"><thead><tr>'
            + "".join(head) + "</tr></thead><tbody>" + "".join(rows) + "</tbody></table></div>")


def timetable_inner(P, res, live=False):
    sems = sorted(P.sems)
    ok = res["failed"] == 0
    verdict = (f"All {res['passed']} hard-constraint checks passed - no faculty, room or laboratory clashes."
               if ok else f"{res['failed']} of {len(res['checks'])} checks failed - see the note below the grid.")
    tabs = "".join(f'<button class="tab{" is-active" if i == 0 else ""}" data-sem="sem{s}">Semester {s}</button>'
                   for i, s in enumerate(sems))
    grids = "".join(sem_table(P, res, s).replace('class="grid-wrap sem-grid"',
                                                  'class="grid-wrap sem-grid is-active"' if s == sems[0] else
                                                  'class="grid-wrap sem-grid"') for s in sems)
    info = res["info"]
    fine = (f"Generated from the uploaded dataset by a Genetic Algorithm "
            f"(lab placement + theory placement; {info['generations']} generations, "
            f"fitness {info['fitness']:.4f}, {res['seconds']}s).")
    if not ok:
        fine += " Failed: " + " | ".join(f"{n}: {d}" for n, okc, d in res["checks"] if not okc)
    return (f'<header class="view-head"><p class="eyebrow">Step 2</p><h1>Generated timetable</h1>'
            f'<p class="lede">Theory in amber, labs in teal. {esc(verdict)}</p></header>'
            + master_html(P, res) +
            f'<div class="panel-head" style="margin-top:28px"><h2>Semester-wise view</h2></div>'
            f'<div class="tabs" role="tablist">{tabs}</div>{grids}'
            f'<p class="fineprint">{esc(fine)}</p>'
            + ('<p class="fineprint"><a class="btn btn-quiet" href="/api/timetable.xlsx" '
               'download="timetable.xlsx">Download master &amp; semester timetables (.xlsx)</a></p>' if live else "")
)


def fragments(P, res):
    n_fac = len(set(P.teaches) | P.faculty_sheet_keys)
    years = len(P.sems)
    stats = (
        f'<div class="stat"><span class="stat-value">{P.n_scheduled_rows:02d}</span>'
        f'<span class="stat-label">Subjects mapped</span><span class="stat-sub">across {years} semesters</span></div>'
        f'<div class="stat"><span class="stat-value">{n_fac:02d}</span>'
        f'<span class="stat-label">Faculty on record</span><span class="stat-sub">availability captured</span></div>'
        f'<div class="stat"><span class="stat-value">{len(P.classrooms) + len(P.labs):02d}</span>'
        f'<span class="stat-label">Rooms ready</span><span class="stat-sub">{len(P.classrooms)} classrooms · '
        f'{len(P.labs)} laboratories</span></div>'
        f'<div class="stat stat-flag"><span class="stat-value">{P.flag_rows:02d}</span>'
        f'<span class="stat-label">Rows to review</span><span class="stat-sub">see the data checks</span></div>')

    if P.notes:
        checks = "".join(f"<li><strong>{esc(t)}</strong><span>{esc(x)}</span></li>" for t, x in P.notes)
    else:
        checks = "<li><strong>No issues found</strong><span>The dataset passed every check.</span></li>"

    low = sorted(P.sems)[0]
    items = []
    if low in res["theory"]:
        for sl, e in enumerate(res["theory"][low][0]):
            if e:
                h, m = divmod(P.theory_rng[sl][0], 60)
                items.append((P.theory_rng[sl][0], f"{h:02d}:{m:02d}", theory_card(e)))
    for r in res["rounds"]:
        if r.sem == low and r.day == 0:
            h, m = divmod(P.lab_rng[r.block][0], 60)
            items.append((P.lab_rng[r.block][0], f"{h:02d}:{m:02d}", lab_cards(P, r)))
    items.sort(key=lambda x: x[0])
    glimpse = "".join(f'<li><span class="glimpse-time">{t}</span>{c}</li>' for _, t, c in items) or \
        '<li><span class="glimpse-time">—</span><span class="slot-chip free">No classes</span></li>'

    rows = []
    for r in P.table_rows:
        cls = ' class="is-flagged"' if r["flagged"] else ""
        rows.append(f'<tr{cls}><td>{r["sem"]}</td><td>{esc(r["year"])}</td><td>{esc(r["subject"])}</td>'
                    f'<td>{esc(r["faculty"]) or "<span class=\"cell-empty\">TBA</span>"}</td>'
                    f'<td>{esc(r["type"])}</td><td>{esc(r["marks"]) or "<span class=\"cell-empty\">missing</span>"}</td>'
                    f'<td>{r["theory"]}</td><td>{esc(r["lab"])}</td></tr>')

    rooms = "".join(f"<tr><td>{esc(n)}</td><td>{esc(t)}</td><td>{c}</td><td>{esc(u)}</td></tr>"
                    for n, t, c, u in P.room_info)
    by_t = defaultdict(lambda: [[], set()])
    for k, lst in P.teaches.items():
        for subj, sem in lst:
            if subj not in by_t[k][0]:
                by_t[k][0].append(subj)
            by_t[k][1].add((sem + 1) // 2)
    fac = "".join(f"<tr><td>{esc(P.disp.get(k, k))}</td><td>{esc(' · '.join(v[0]))}</td>"
                  f"<td>{esc(', '.join(ordinal(y) for y in sorted(v[1])))}</td></tr>"
                  for k, v in sorted(by_t.items(), key=lambda kv: P.disp.get(kv[0], kv[0]).lower()))

    return dict(ok=True, stats=stats, checks=checks, flagged=len(P.notes), glimpse=glimpse,
                glimpse_tag=f"Semester {low}", rows=len(P.table_rows), dataset_rows="".join(rows),
                timetable=timetable_inner(P, res, True), rooms=rooms, faculty=fac,
                clean=res["failed"] == 0, passed=res["passed"], failed=res["failed"],
                seconds=res["seconds"],
                checks_detail=[dict(name=n, ok=o, detail=d) for n, o, d in res["checks"]])


def generate_from(source, filename="dataset.xlsx", seed=42, log=print):
    sheets = read_sheets(source, filename)
    P = load_problem(sheets)
    log(f"  semesters {sorted(P.sems)} | classrooms {P.classrooms} | labs {P.labs}")
    res = solve(P, seed=seed, log=log)
    return P, res


# ============================================================================
# 7b. MASTER TIMETABLE + SEMESTER TIMETABLES  (page and Excel share the same data)
# ============================================================================
def sem_label(sem):
    return f"{ordinal(sem)} Sem"


def build_master(P, res):
    """[(day, [(sem, [cell,...]), ...]), ...]  one row per semester per day, 7 theory columns.
    A lab becomes one merged cell spanning the theory periods it occupies."""
    ns = len(P.theory_slots)
    out = []
    for d, dn in enumerate(P.days):
        rows = []
        for sem in sorted(P.sems):
            lab = next((r for r in res["rounds"] if r.sem == sem and r.day == d), None)
            blocked = P.block_slots[lab.block] if lab else frozenset()
            cells, sl = [], 0
            while sl < ns:
                if sl in blocked:
                    c1 = sl
                    while c1 + 1 < ns and (c1 + 1) in blocked:
                        c1 += 1
                    cells.append(dict(kind="lab", c0=sl, c1=c1, round=lab))
                    sl = c1 + 1
                else:
                    e = res["theory"][sem][d][sl] if sem in res["theory"] else None
                    cells.append(dict(kind="theory" if e else "free", c0=sl, c1=sl, e=e))
                    sl += 1
            rows.append((sem, cells))
        out.append((dn, rows))
    return out


def master_text(P, c):
    if c["kind"] == "theory":
        return f"{c['e']['subject']} – {c['e']['room']}\n{c['e']['faculty']}"
    if c["kind"] == "lab":
        r = c["round"]
        lines = [f"LAB ({pretty_range(P.lab_slots[r.block])})"]
        for e in r.entries:
            team = " & ".join(P.disp.get(k, k) for k in e["team"])
            lines.append(f"B{e['bi'] + 1}: {e['sub'].lab_name} ({e['lab_room']}) – {team}")
        return "\n".join(lines)
    return ""


def master_html(P, res):
    head = ('<th class="tt-time">DAYS</th><th class="tt-time">SEMESTERS</th>'
            + "".join(f"<th>{esc(pretty_range(x))}</th>" for x in P.theory_slots))
    body = []
    for dn, rows in build_master(P, res):
        for i, (sem, cells) in enumerate(rows):
            tds = ""
            if i == 0:
                tds += f'<td class="tt-time" rowspan="{len(rows)}"><strong>{esc(dn.upper())}</strong></td>'
            tds += f'<td class="tt-time">{esc(sem_label(sem))}</td>'
            for c in cells:
                span = c["c1"] - c["c0"] + 1
                if c["kind"] == "lab":
                    tds += f'<td colspan="{span}">{lab_cards(P, c["round"])}</td>'
                elif c["kind"] == "theory":
                    tds += f"<td>{theory_card(c['e'])}</td>"
                else:
                    tds += '<td><span class="slot-chip free">—</span></td>'
            body.append(f"<tr>{tds}</tr>")
    return ('<div class="panel-head"><h2>Master timetable</h2>'
            '<span class="panel-tag">all semesters</span></div>'
            f'<div class="grid-wrap"><table class="tt-grid"><thead><tr>{head}</tr></thead>'
            f'<tbody>{"".join(body)}</tbody></table></div>')


def sem_text(P, e):
    return f"{e['subject']} – {e['room']}\n{e['faculty']}" if e else None


def sem_lab_text(P, r):
    lines = [f"LAB ({pretty_range(P.lab_slots[r.block])})"]
    for e in r.entries:
        team = " & ".join(P.disp.get(k, k) for k in e["team"])
        lines.append(f"B{e['bi'] + 1}: {e['sub'].lab_name} ({e['lab_room']}) – {team}")
    return "\n".join(lines)


def write_timetable_xlsx(P, res, target):
    """Workbook: 'Master Timetable' + one sheet per semester. target: path or file-like."""
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Border, Font, Side
    wb = Workbook()
    thin = Side(style="thin")
    box = Border(left=thin, right=thin, top=thin, bottom=thin)
    FONT = "Aptos Narrow"
    ns = len(P.theory_slots)

    def style(ws, nrows, ncols, first_cols):
        for row in ws.iter_rows(min_row=1, max_row=nrows, max_col=ncols):
            for c in row:
                c.border = box
                c.font = Font(name=FONT, size=11, bold=c.row == 1 or c.column <= first_cols or
                              c.value is not None)
                c.alignment = Alignment(horizontal="center" if (c.row == 1 or c.column == 1) else None,
                                        vertical="center", wrap_text=True)

    # ---- master -------------------------------------------------------------
    ms = wb.active
    ms.title = "Master Timetable"
    ms.append(["DAYS", "SEMESTERS"] + [pretty_range(x) for x in P.theory_slots])
    r0 = 2
    for dn, rows in build_master(P, res):
        for sem, cells in rows:
            ms.cell(row=r0, column=2, value=sem_label(sem))
            for c in cells:
                ms.cell(row=r0, column=c["c0"] + 3, value=master_text(P, c) or None)
            r0 += 1
    ncols = ns + 2
    style(ms, r0 - 1, ncols, 2)
    r = 2
    for dn, rows in build_master(P, res):
        ms.cell(row=r, column=1, value=dn.upper())
        ms.merge_cells(start_row=r, start_column=1, end_row=r + len(rows) - 1, end_column=1)
        for sem, cells in rows:
            for c in cells:
                if c["c1"] > c["c0"]:
                    ms.merge_cells(start_row=r, start_column=c["c0"] + 3, end_row=r, end_column=c["c1"] + 3)
            narrow_lab = any(c["kind"] == "lab" and c["c1"] == c["c0"] for c in cells)
            ms.row_dimensions[r].height = 110 if narrow_lab else 62
            r += 1
    ms.row_dimensions[1].height = 28.8
    ms.column_dimensions["A"].width = 17
    ms.column_dimensions["B"].width = 15
    for ci in range(3, ncols + 1):
        ms.column_dimensions[chr(64 + ci)].width = 27
    ms.column_dimensions[chr(64 + ncols)].width = 44

    # ---- one sheet per semester (Day x periods + Lab Block) -------------------
    for sem in sorted(P.sems):
        ws = wb.create_sheet(sem_label(sem))
        ws.append(["Day"] + [pretty_range(x) for x in P.theory_slots] + ["Lab Block"])
        for d, dn in enumerate(P.days):
            row = [dn]
            for sl in range(ns):
                e = res["theory"][sem][d][sl] if sem in res["theory"] else None
                row.append(sem_text(P, e))
            lab = next((x for x in res["rounds"] if x.sem == sem and x.day == d), None)
            row.append(sem_lab_text(P, lab) if lab else "—")
            ws.append(row)
        style(ws, len(P.days) + 1, ns + 2, 1)
        ws.row_dimensions[1].height = 28.8
        for ri in range(2, len(P.days) + 2):
            ws.row_dimensions[ri].height = 62
        ws.column_dimensions["A"].width = 14
        for ci in range(2, ns + 2):
            ws.column_dimensions[chr(64 + ci)].width = 24
        ws.column_dimensions[chr(64 + ns + 2)].width = 44
    wb.save(target)


# ============================================================================
# 8. LIVE PAGE: served index.html + injected drag-and-drop glue
#    (index.html and styles.css on disk are never modified)
# ============================================================================
INJECT = r"""
<script id="tt-live">
(function () {
  let chosen = null;
  const $ = (s, r) => (r || document).querySelector(s);
  const dz = $('#dropzone'), status = $('#fileStatus');
  const oldBtn = $('#generateBtn'), hint = $('#generateHint');
  const btn = oldBtn.cloneNode(true);            // drop the mock click handler
  oldBtn.replaceWith(btn);

  function setStatus(msg, bad) {
    status.textContent = msg;
    status.style.color = bad ? 'var(--warn)' : '';
  }

  function apply(f) {
    $('.stat-strip').innerHTML = f.stats;
    $('.panel-checks .check-list').innerHTML = f.checks;
    const tag = $('.panel-checks .panel-tag');
    tag.textContent = f.flagged ? f.flagged + ' flagged' : 'all clear';
    tag.classList.toggle('panel-tag-warn', f.flagged > 0);
    $('.glimpse-list').innerHTML = f.glimpse;
    $('.panel-glimpse .panel-tag').textContent = f.glimpse_tag;
    $('#upload .data-table tbody').innerHTML = f.dataset_rows;
    $('#upload .panel-tag').textContent = f.rows + ' rows';
    $('#timetable').innerHTML = f.timetable;
    const bodies = document.querySelectorAll('#resources .data-table tbody');
    if (bodies[0]) bodies[0].innerHTML = f.rooms;
    if (bodies[1]) bodies[1].innerHTML = f.faculty;
  }

  // semester tabs inside the regenerated timetable
  $('#timetable').addEventListener('click', e => {
    const t = e.target.closest('.tab');
    if (!t) return;
    document.querySelectorAll('#timetable .tab').forEach(x => x.classList.remove('is-active'));
    document.querySelectorAll('#timetable .sem-grid').forEach(x => x.classList.remove('is-active'));
    t.classList.add('is-active');
    document.getElementById(t.dataset.sem).classList.add('is-active');
  });

  async function run() {
    btn.disabled = true;
    btn.textContent = 'Generating…';
    hint.textContent = 'Running the genetic algorithm and validating every constraint';
    try {
      const url = chosen ? '/api/generate' : '/api/generate?sample=1';
      const res = await fetch(url, {
        method: 'POST',
        headers: { 'X-Filename': encodeURIComponent(chosen ? chosen.name : 'sample') },
        body: chosen || ''
      });
      const f = await res.json();
      if (!f.ok) throw new Error(f.error || 'Generation failed');
      apply(f);
      hint.textContent = f.clean
        ? 'Done - ' + f.passed + ' constraint checks passed, 0 clashes (' + f.seconds + 's)'
        : 'Generated with ' + f.failed + ' failed check(s) - see the timetable page';
      setStatus((chosen ? 'Generated from ' + chosen.name : 'Generated from the sample dataset'), false);
      showView('timetable');
    } catch (err) {
      setStatus(String(err.message || err), true);
      hint.textContent = 'Could not generate - fix the dataset and drop it again';
    } finally {
      btn.disabled = false;
      btn.textContent = 'Generate timetable';
    }
  }

  window.handleFiles = function (list) {      // replaces the page's placeholder
    if (!list || !list.length) return;
    const f = Array.from(list).find(x => /\.(xlsx|xlsm|xls)$/i.test(x.name));
    if (!f) { setStatus('Please drop the Excel workbook (.xlsx).', true); return; }
    chosen = f;
    setStatus('Selected: ' + f.name, false);
    run();                                     // drop => timetable
  };
  btn.addEventListener('click', run);
  hint.textContent = 'Drop your dataset above - or press Generate to use the bundled sample';
})();
</script>
"""

_lock = threading.Lock()
LAST = {}


def find_existing(names):
    for n in names:
        p = BASE_DIR / n
        if p.exists():
            return p
    return None


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = urlparse(self.path).path
        if path in ("/", "/index.html"):
            f = find_existing(HTML_NAMES)
            if not f:
                return self._send(404, "index.html not found next to the script", "text/plain")
            text = f.read_text(encoding="utf-8")
            if 'id="p-generate"' not in text:          # the mLAC site has its own built-in glue
                text = text.replace("</body>", INJECT + "\n</body>", 1) if "</body>" in text else text + INJECT
            return self._send(200, text, "text/html; charset=utf-8")
        if path == "/api/timetable.xlsx":
            if "P" not in LAST:
                return self._send(404, "Generate a timetable first.", "text/plain")
            buf = io.BytesIO()
            with _lock:
                write_timetable_xlsx(LAST["P"], LAST["res"], buf)
            return self._send(200, buf.getvalue(),
                              "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
        if path == "/styles.css":
            f = find_existing(CSS_NAMES)
            if f:
                return self._send(200, f.read_bytes(), "text/css; charset=utf-8")
        self._send(404, "Not found", "text/plain")

    def do_POST(self):
        u = urlparse(self.path)
        if u.path != "/api/generate":
            return self._send(404, "Not found", "text/plain")
        n = int(self.headers.get("Content-Length") or 0)
        body = self.rfile.read(n) if n else b""
        name = unquote(self.headers.get("X-Filename", "dataset.xlsx"))
        try:
            with _lock:
                if not body:
                    sample = find_existing(SAMPLE_NAMES)
                    if not sample:
                        raise ValueError("No sample dataset next to the script. Drop your own workbook.")
                    P, res = generate_from(sample)
                else:
                    P, res = generate_from(body, name)
            out = fragments(P, res)
            LAST["P"], LAST["res"] = P, res
        except Exception as ex:                                   # shown in the page
            out = dict(ok=False, error=f"{type(ex).__name__}: {ex}")
        self._send(200, json.dumps(out), "application/json")


def serve():
    port = PORT
    for p in range(PORT, PORT + 20):
        try:
            srv = ThreadingHTTPServer(("127.0.0.1", p), Handler)
            port = p
            break
        except OSError:
            continue
    else:
        raise SystemExit("No free port found.")
    url = f"http://127.0.0.1:{port}/"
    print("Starting timetable generator...")
    print(f"Opening: {url}")
    webbrowser.open_new_tab(url)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")


def static_output(path):
    P, res = generate_from(Path(path))
    f = find_existing(HTML_NAMES)
    template = f.read_text(encoding="utf-8")
    section = ('<section id="timetable" class="view">' + timetable_inner(P, res) + "</section>")
    pat = re.compile(r'<section\s+id=["\']timetable["\'][^>]*>.*?</section>', re.I | re.S)
    if pat.search(template):
        page = pat.sub(lambda m: section, template, count=1)
    elif '<div id="out"></div>' in template:       # mLAC multi-page site: fill the Generate page
        page = template.replace('<div id="out"></div>', '<div id="out">' + timetable_inner(P, res) + '</div>', 1)
        page = page.replace("</body>", "<script>location.hash='#generate';</script></body>", 1)
        page = page.replace("const out=$('out')", "const out=$('out')")
    else:
        raise ValueError('index.html has neither <section id="timetable"> nor the Generate page.')
    OUTPUT_FILE.write_text(page, encoding="utf-8")
    print(f"Timetable generated: {OUTPUT_FILE.name}")
    print(f"Checks: {res['passed']} passed, {res['failed']} failed")
    webbrowser.open_new_tab(OUTPUT_FILE.resolve().as_uri())


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="Smart timetable generator (Genetic Algorithm)")
    ap.add_argument("--dataset", help="generate Generated_Timetable.html directly from this workbook")
    a = ap.parse_args()
    if a.dataset:
        static_output(a.dataset)
    else:
        serve()