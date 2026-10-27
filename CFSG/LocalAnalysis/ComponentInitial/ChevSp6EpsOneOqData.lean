module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchBits
public import Mathlib.Data.List.Sort

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits)

@[expose] def evalV (l : List ℕ) (v : ℕ) : ℕ := xorBits 6 (fun j => l.getD j 0) v

@[expose] def evalE (l : List ℕ) (e : ℕ) : ℕ := xorBits 9 (fun j => l.getD j 0) e

@[expose] def compT (a b : List ℕ) : List ℕ := b.map (evalV a)

@[expose] def idT : List ℕ := [1, 2, 4, 8, 16, 32]

@[expose] def wpart (v : ℕ) : ℕ := (v &&& 1) ||| ((v >>> 1) &&& 2) ||| ((v >>> 2) &&& 4)

@[expose] def xpart (v : ℕ) : ℕ := ((v >>> 1) &&& 1) ||| ((v >>> 2) &&& 2) ||| ((v >>> 3) &&& 4)

@[expose] def mkv (w x : ℕ) : ℕ :=
  (w &&& 1) ||| ((w &&& 2) <<< 1) ||| ((w &&& 4) <<< 2) |||
    ((x &&& 1) <<< 1) ||| ((x &&& 2) <<< 2) ||| ((x &&& 4) <<< 3)

@[expose] def outer (a b : ℕ) : ℕ :=
  (if a.testBit 0 then b &&& 7 else 0) ^^^ (if a.testBit 1 then (b &&& 7) <<< 3 else 0) ^^^
    (if a.testBit 2 then (b &&& 7) <<< 6 else 0)

@[expose] def qOf (u : Bool) (v : ℕ) : ℕ :=
  outer (wpart v) (wpart v) ^^^ outer (wpart v) (xpart v) ^^^
    (if u then outer (xpart v) (xpart v) else 0)

@[expose] def betaOf (u : Bool) (v w : ℕ) : ℕ := qOf u (v ^^^ w) ^^^ qOf u v ^^^ qOf u w

@[expose] def z0T : List ℕ := (List.range 6).map fun j =>
  mkv (wpart (2 ^ j) ^^^ xpart (2 ^ j)) (xpart (2 ^ j))

@[expose] def ev3 (g : List ℕ) (a : ℕ) : ℕ := xorBits 3 (fun j => g.getD j 0) a

@[expose] def diagT (g : List ℕ) : List ℕ := (List.range 6).map fun j =>
  mkv (ev3 g (wpart (2 ^ j))) (ev3 g (xpart (2 ^ j)))

@[expose] def g1C : List ℕ := [1, 3, 4]

@[expose] def g2C : List ℕ := [2, 4, 1]

@[expose] def lam1T : List ℕ := diagT g1C

@[expose] def lam2T : List ℕ := diagT g2C

@[expose] def lmRed (rows : List (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ × ℕ :=
  rows.foldl (fun p r => if p.1 ^^^ r.1 < p.1 then (p.1 ^^^ r.1, p.2 ^^^ r.2) else p) p

@[expose] def lmAdd (rows : List (ℕ × ℕ)) (x y : ℕ) : Option (List (ℕ × ℕ)) :=
  let p := lmRed rows (x, y)
  if p.1 = 0 then (if p.2 = 0 then some rows else none)
  else some (rows.orderedInsert (fun a b => b.1 ≤ a.1) p)

@[expose] def addNew (u : Bool) (imgs : List ℕ) (k : ℕ) (rows : List (ℕ × ℕ)) :
    Option (List (ℕ × ℕ)) :=
  (List.range (2 ^ k)).foldl (fun acc u₀ => acc.bind fun rs =>
    if evalV imgs (2 ^ k + u₀) = 0 then none
    else lmAdd rs (qOf u (2 ^ k + u₀)) (qOf u (evalV imgs (2 ^ k + u₀)))) (some rows)

@[expose] def fibTab (u : Bool) : Array (List ℕ) :=
  (List.range 512).toArray.map fun y => (List.range 64).filter fun v => qOf u v == y

@[expose] def fibL : Array (List ℕ) := fibTab false

@[expose] def fibU : Array (List ℕ) := fibTab true

@[expose] def fibOf (u : Bool) : Array (List ℕ) := if u then fibU else fibL

@[expose] def cands (u : Bool) (k : ℕ) (rows : List (ℕ × ℕ)) : List ℕ :=
  if (lmRed rows (qOf u (2 ^ k), 0)).1 = 0 then (fibOf u).getD (lmRed rows (qOf u (2 ^ k), 0)).2 []
  else List.range 64

@[expose] def oqStep (u : Bool) (k : ℕ) (st : List ℕ × List (ℕ × ℕ)) :
    List (List ℕ × List (ℕ × ℕ)) :=
  (cands u k st.2).filterMap fun t =>
    (addNew u (st.1 ++ [t]) k st.2).map fun rs => (st.1 ++ [t], rs)

@[expose] def oqStatesFrom (u : Bool) (t₀ m : ℕ) : List (List ℕ × List (ℕ × ℕ)) :=
  (List.range m).foldl (fun acc k => acc.flatMap (oqStep u (k + 1)))
    ((addNew u [t₀] 0 []).map fun rs => ([t₀], rs)).toList

@[expose] def oqFrom (u : Bool) (t₀ : ℕ) : List (List ℕ) := (oqStatesFrom u t₀ 5).map Prod.fst

@[expose] def oqSearch (u : Bool) : List (List ℕ) := (List.range 64).flatMap (oqFrom u)

@[expose] def spanW (u : Bool) : List (ℕ × ℕ × ℕ) := (List.range 9).map fun k =>
  if k / 3 = k % 3 then (mkv (2 ^ (k / 3)) 0, 0, 0)
  else (mkv (2 ^ (k / 3)) (2 ^ (k % 3)), mkv (2 ^ (k / 3)) 0,
    if u then mkv 0 (2 ^ (k % 3)) else 0)

@[expose] def bOf (u : Bool) (l : List ℕ) : List ℕ := (spanW u).map fun t =>
  qOf u (evalV l t.1) ^^^ qOf u (evalV l t.2.1) ^^^ qOf u (evalV l t.2.2)

@[expose] def validT (u : Bool) (l : List ℕ) : Bool :=
  let B := bOf u l
  l.length == 6 && l.all (· < 64) &&
    (List.range 64).all (fun v => v == 0 || evalV l v != 0) &&
    (List.range 64).all (fun v => qOf u (evalV l v) == evalE B (qOf u v))

@[expose] def codeT (l : List ℕ) : ℕ := l.foldl (fun r a => 64 * r + a) 0

@[expose] def strictSorted : List ℕ → Bool
  | a :: b :: l => a < b && strictSorted (b :: l)
  | _ => true

@[expose] def oqCount (u : Bool) (t : ℕ) : ℕ :=
  if t = 0 then 0 else if u then 5760 else if qOf false t = 0 then 0 else 1152

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
