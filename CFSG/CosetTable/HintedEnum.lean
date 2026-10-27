module

public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.CosetTable

@[expose] def defStep (P : Params) (fuel c x : Nat) (st : St) : St :=
  if st.tab.getD (c * P.L + x) 0 == 0 then processDed P fuel (define P st c x) else st

@[expose] def defPath (P : Params) (fuel : Nat) : Nat → List Nat → St → St × Nat
  | c, [], st => (st, find st.fwd st.next c)
  | c, x :: w, st =>
    let c := find st.fwd st.next c
    let st := defStep P fuel c x st
    let d := st.tab.getD (c * P.L + x) 0
    if d == 0 then (st, c) else defPath P fuel d w st

@[expose] def hltHint (P : Params) (fuel : Nat) (p : List Nat × List Nat) (st : St) : St :=
  if p ∈ P.rels then processDed P fuel (hltWord P 1 p.1 p.2 (p.1.length + 1) st) else st

@[expose] def fillRowLim (P : Params) (fuel c lim : Nat) : Nat → St → St
  | 0, st => st
  | n + 1, st =>
    if st.overflow || st.fwd.getD c c != c then st
    else
      let x := lim - (n + 1)
      if st.tab.getD (c * P.L + x) 0 == 0 then
        fillRowLim P fuel c lim n (processDed P fuel (define P st c x))
      else fillRowLim P fuel c lim n st

@[expose] def felschLim (P : Params) (fuel lim : Nat) : Nat → Nat → St → St
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then
      felschLim P fuel lim n (c + 1) (fillRowLim P fuel c lim lim st)
    else st

@[expose] def Params.restrict (P : Params) (idx : List Nat) : Params :=
  if idx.isEmpty then P
  else { P with scans :=
    (mkParams P.L P.inv (idx.map fun i => (P.rels.getD i ([], [])).1) []).scans }

structure Block where
  path : List Nat
  rels : List (List Nat)
  lim : Nat
  scan : List Nat

structure Hints where
  blocks : List Block
  late : Nat
  lateScan : List Nat
  kCol : Nat
  kScan : List Nat

@[expose] def pushColumn (P : Params) (x : Nat) : Nat → St → St
  | 0, st => st
  | c + 1, st =>
    pushColumn P x c
      (if 0 < c && st.fwd.getD c c == c && st.tab.getD (c * P.L + x) 0 != 0 then
        { st with ded := st.ded.push (c * P.L + x) }
      else st)

@[expose] def runBlock (P : Params) (cap fuel : Nat) (b : Block) (st : St) : St :=
  let Q := P.restrict b.scan
  let r := defPath Q fuel 1 b.path st
  felschLim Q fuel b.lim (cap + 1) r.2
    (b.rels.foldl (fun st w => hltHint Q fuel (w, invWord Q.inv w) st) r.1)

@[expose] def enumerateHinted (P : Params) (cap : Nat) (H : Hints) : St :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  let st := H.blocks.foldl (fun st b => runBlock P cap fuel b st)
    (fillSubs P fuel P.subs (St.init P.L cap))
  let st := felschLim (P.restrict H.lateScan) fuel H.late (cap + 1) 1 st
  let Q := P.restrict H.kScan
  felsch P fuel (cap + 1) 1 (processDed Q fuel (pushColumn Q H.kCol st.next st))

@[expose] def checkHinted (P : Params) (H : Hints) (cap n : Nat) : Bool :=
  let st := enumerateHinted P cap H
  !st.overflow && st.complete P.L && st.liveCount == n

end CFSG.CosetTable
