module

public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

open CFSG.Monster.B.Fischer

@[expose] def sumLt (n : ℕ) (f : ℕ → ℕ) : ℕ := ((List.range n).map f).sum

@[expose] def eA (n : ℕ) (x : Array ℕ) (i j : ℕ) : ℕ := x[n * i + j]!

@[expose] def eB (n : ℕ) (x : Array ℕ) (i j : ℕ) : ℕ := x[n * n + (n * i + j)]!

@[expose] def eE (n : ℕ) (x : Array ℕ) : ℕ := x[2 * (n * n)]!

@[expose] def eltMul (n : ℕ) (x y : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 2 * (n * n) + 1) fun k =>
    if (k : ℕ) < n * n then
      sumLt n (fun l => eA n x ((k : ℕ) / n) l *
        (if eE n x = 1 then eB n y l ((k : ℕ) % n) else eA n y l ((k : ℕ) % n))) % 3
    else if (k : ℕ) < 2 * (n * n) then
      sumLt n (fun l => eB n x (((k : ℕ) - n * n) / n) l *
        (if eE n x = 1 then eA n y l (((k : ℕ) - n * n) % n)
          else eB n y l (((k : ℕ) - n * n) % n))) % 3
    else (eE n x + eE n y) % 2

@[expose] def eltOne (n : ℕ) : Array ℕ :=
  Array.ofFn (n := 2 * (n * n) + 1) fun k =>
    if (k : ℕ) < 2 * (n * n) then
      (if ((k : ℕ) % (n * n)) / n = ((k : ℕ) % (n * n)) % n then 1 else 0)
    else 0

@[expose] def eltInv (n : ℕ) (x : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 2 * (n * n) + 1) fun k =>
    if (k : ℕ) < n * n then
      (if eE n x = 1 then eA n x ((k : ℕ) % n) ((k : ℕ) / n) else eB n x ((k : ℕ) % n) ((k : ℕ) / n))
    else if (k : ℕ) < 2 * (n * n) then
      (if eE n x = 1 then eB n x (((k : ℕ) - n * n) % n) (((k : ℕ) - n * n) / n)
        else eA n x (((k : ℕ) - n * n) % n) (((k : ℕ) - n * n) / n))
    else eE n x

@[expose] def eltValid (n : ℕ) (x : Array ℕ) : Bool :=
  x.size == 2 * (n * n) + 1 && (List.range (2 * (n * n))).all (fun k => decide (x[k]! < 3)) &&
    decide (x[2 * (n * n)]! < 2) &&
    (List.range n).all (fun i => (List.range n).all (fun j =>
      sumLt n (fun l => eA n x i l * eB n x j l) % 3 == (if i == j then 1 else 0)))

@[expose] def ePow (n : ℕ) (x : Array ℕ) : ℕ → Array ℕ
  | 0 => eltOne n
  | m + 1 => eltMul n (ePow n x m) x

@[expose] def eltEq (n : ℕ) (x y : Array ℕ) : Bool :=
  (eE n x == eE n y) &&
    ((List.range (n * n)).all (fun k => x[k]! % 3 == y[k]! % 3) ||
      (List.range (n * n)).all (fun k => (x[k]! + y[k]!) % 3 == 0))

@[expose] def evalWord (n : ℕ) (ws : Array (Array ℕ)) (w : List (ℕ × Bool)) : Array ℕ :=
  w.foldl (fun acc l => eltMul n acc (if l.2 then eltInv n ws[l.1]! else ws[l.1]!)) (eltOne n)

structure LocRep where
  x : Array ℕ
  t : Array ℕ
  g₁ : Array ℕ
  g₂ : Array ℕ
  wa : List (ℕ × Bool)
  wb : List (ℕ × Bool)
  ma : ℕ
  mb : ℕ
  j : ℕ
  deriving Inhabited

@[expose] def eltConj (n : ℕ) (s x : Array ℕ) : Array ℕ := eltMul n (eltMul n s x) (eltInv n s)

@[expose] def repOK (n : ℕ) (inF : Array ℕ → Bool) (r : LocRep) : Bool :=
  eltValid n r.x && eltValid n r.t && eltValid n r.g₁ && eltValid n r.g₂ &&
    inF r.g₁ && inF r.g₂ && (eE n r.g₁ == 0) && (eE n r.g₂ == 0) &&
    eltEq n (eltMul n r.g₁ r.t) (eltMul n r.t r.g₁) &&
    eltEq n (eltMul n r.g₂ r.t) (eltMul n r.t r.g₂) &&
    r.wa.all (fun l => decide (l.1 < 3)) && r.wb.all (fun l => decide (l.1 < 3)) &&
    (r.ma % 2 == 1) && (r.mb % 2 == 1) &&
    eltEq n (ePow n (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wa) r.ma)
      (eltOne n) &&
    eltEq n (ePow n (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wb) r.mb)
      (eltOne n) &&
    eltEq n (ePow n (eltMul n (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wa)
      (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wb)) (2 * r.j)) (eltOne n) &&
    !eltEq n (ePow n (eltMul n (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wa)
      (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wb)) r.j) (eltOne n)

@[expose] def kA (n : ℕ) (x : Array ℕ) : ℕ :=
  Nat.ofDigits 3 ((List.range (n * n)).map fun k => x[k]! % 3)

@[expose] def kN (n : ℕ) (x : Array ℕ) : ℕ :=
  Nat.ofDigits 3 ((List.range (n * n)).map fun k => (3 - x[k]! % 3) % 3)

@[expose] def eltKey (n : ℕ) (x : Array ℕ) : ℕ := 2 * min (kA n x) (kN n x) + eE n x % 2

@[expose] def eltMinusOne (n : ℕ) : Array ℕ :=
  Array.ofFn (n := 2 * (n * n) + 1) fun k =>
    if (k : ℕ) < 2 * (n * n) then
      (if ((k : ℕ) % (n * n)) / n = ((k : ℕ) % (n * n)) % n then 2 else 0)
    else 0

@[expose] def firstNZ (n : ℕ) (x : Array ℕ) : ℕ :=
  match (List.range (n * n)).find? (fun k => x[k]! % 3 != 0) with
  | some k => x[k]! % 3
  | none => 0

@[expose] def eltNorm (n : ℕ) (x : Array ℕ) : Array ℕ :=
  if firstNZ n x == 2 then eltMul n (eltMinusOne n) x else x

@[expose] def det4Z (x : Array ℕ) : ℤ :=
  let m := fun (i j : ℕ) => (x[4 * i + j]! : ℤ)
  m 0 0 * (m 1 1 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 1 * m 3 3 - m 2 3 * m 3 1) +
      m 1 3 * (m 2 1 * m 3 2 - m 2 2 * m 3 1)) -
    m 0 1 * (m 1 0 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 0 * m 3 3 - m 2 3 * m 3 0) +
      m 1 3 * (m 2 0 * m 3 2 - m 2 2 * m 3 0)) +
    m 0 2 * (m 1 0 * (m 2 1 * m 3 3 - m 2 3 * m 3 1) - m 1 1 * (m 2 0 * m 3 3 - m 2 3 * m 3 0) +
      m 1 3 * (m 2 0 * m 3 1 - m 2 1 * m 3 0)) -
    m 0 3 * (m 1 0 * (m 2 1 * m 3 2 - m 2 2 * m 3 1) - m 1 1 * (m 2 0 * m 3 2 - m 2 2 * m 3 0) +
      m 1 2 * (m 2 0 * m 3 1 - m 2 1 * m 3 0))

@[expose] def inF4 (x : Array ℕ) : Bool := det4Z x % 3 == 1

@[expose] def inF5 (_ : Array ℕ) : Bool := true

structure LocData where
  gens : Array (Array ℕ)
  reps : Array LocRep
  fuel : ℕ
  k : ℕ

@[expose] def locAct (n : ℕ) (gens : Array (Array ℕ)) (k : ℕ) (a : Array ℕ) : Array ℕ :=
  eltNorm n (eltMul n gens[k]! a)

@[expose] def locBfs (n : ℕ) (d : LocData) : ArrCert :=
  arrBfs (locAct n d.gens) d.gens.size (eltKey n) (eltOne n) d.fuel

@[expose] def isO8 (n : ℕ) (x : Array ℕ) : Bool :=
  eltEq n (ePow n x 8) (eltOne n) && !eltEq n (ePow n x 4) (eltOne n)

@[expose] def isO2 (n : ℕ) (t : Array ℕ) : Bool :=
  eltEq n (ePow n t 2) (eltOne n) && !eltEq n t (eltOne n)

@[expose] def locIdx (n : ℕ) (pts : Array (Array ℕ)) : Std.HashMap ℕ ℕ :=
  (List.range pts.size).foldl (fun m i => m.insert (eltKey n pts[i]!) i) ∅

@[expose] def locCov (n : ℕ) (pts : Array (Array ℕ)) (reps : Array LocRep) :
    Std.HashMap (ℕ × ℕ) (ℕ × ℕ) :=
  let idx := locIdx n pts
  (List.range reps.size).foldl (fun m ri =>
    (List.range pts.size).foldl (fun m si =>
      match idx.get? (eltKey n (eltConj n pts[si]! reps[ri]!.x)),
          idx.get? (eltKey n (eltConj n pts[si]! reps[ri]!.t)) with
      | some ix, some it => m.insert (ix, it) (ri, si)
      | _, _ => m) m) ∅

@[expose] def locCover (n : ℕ) (pts : Array (Array ℕ)) (reps : Array LocRep) : Bool :=
  let cov := locCov n pts reps
  let o8 := (List.range pts.size).filter fun i => isO8 n pts[i]!
  let o2 := (List.range pts.size).filter fun j => isO2 n pts[j]!
  o8.all fun i => o2.all fun j =>
    !eltEq n (eltMul n pts[i]! pts[j]!) (eltMul n pts[j]! pts[i]!) ||
      match cov.get? (i, j) with
      | some (ri, si) => decide (ri < reps.size) && decide (si < pts.size) &&
          eltEq n (eltConj n pts[si]! reps[ri]!.x) pts[i]! &&
          eltEq n (eltConj n pts[si]! reps[ri]!.t) pts[j]!
      | none => false

@[expose] def locCheck (n : ℕ) (inF : Array ℕ → Bool) (d : LocData) : Bool :=
  (List.range d.gens.size).all (fun k => eltValid n d.gens[k]!) &&
    arrCertOK (locAct n d.gens) d.gens.size (eltValid n) (eltKey n) (eltOne n) (locBfs n d) &&
    ((locBfs n d).pts.size == 2 ^ d.k) &&
    d.reps.toList.all (repOK n inF) &&
    locCover n (locBfs n d).pts d.reps

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc
