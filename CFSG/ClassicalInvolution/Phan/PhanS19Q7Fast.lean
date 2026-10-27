module

public import CFSG.ClassicalInvolution.Phan.PhanS19Q7Inputs

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

instance instInhabitedN7Q7 : Inhabited N7 := ⟨e0N⟩

@[expose] def tMul : Array Nat := (Array.range 2401).map fun i => gfMul (i / 49) (i % 49)

@[expose] def tAdd : Array Nat := (Array.range 2401).map fun i => gfAdd (i / 49) (i % 49)

@[expose] def tNeg : Array Nat := (Array.range 49).map gfNeg

@[expose] def tConj : Array Nat := (Array.range 49).map gfConj

@[expose] def tNorm : Array Nat := (Array.range 49).map fun a => gfMul a (gfConj a)

@[expose] def tInv : Array Nat :=
  (Array.range 49).map fun a => ((List.range 49).find? fun b => gfMul a b == 1).getD 0

@[expose, inline] def fMul (a b : Nat) : Nat := tMul[a * 49 + b]!

@[expose, inline] def fAdd (a b : Nat) : Nat := tAdd[a * 49 + b]!

@[expose, inline] def fNeg (a : Nat) : Nat := tNeg[a]!

@[expose, inline] def fConj (a : Nat) : Nat := tConj[a]!

@[expose, inline] def fNorm (a : Nat) : Nat := tNorm[a]!

@[expose, inline] def fInv (a : Nat) : Nat := tInv[a]!

@[expose, inline] def hDiag (x : N7) : Nat :=
  fAdd (fAdd (fAdd (fAdd (fAdd (fAdd (fNorm x.x0) (fNorm x.x1)) (fNorm x.x2)) (fNorm x.x3))
    (fNorm x.x4)) (fNorm x.x5)) (fMul 5 (fNorm x.x6))

@[expose, inline] def hF (x y : N7) : Nat :=
  fAdd (fAdd (fAdd (fMul x.x0 (fConj y.x0)) (fMul x.x1 (fConj y.x1)))
      (fAdd (fMul x.x2 (fConj y.x2)) (fMul x.x3 (fConj y.x3))))
    (fAdd (fAdd (fMul x.x4 (fConj y.x4)) (fMul x.x5 (fConj y.x5)))
      (fMul 5 (fMul x.x6 (fConj y.x6))))

@[expose, inline] def bF (x y : N7) : Nat :=
  fAdd (fAdd (fAdd (fAdd (fMul x.x0 y.x3) (fMul y.x0 x.x3))
      (fAdd (fMul x.x1 y.x4) (fMul y.x1 x.x4))) (fAdd (fMul x.x2 y.x5) (fMul y.x2 x.x5)))
    (fMul 5 (fMul x.x6 y.x6))

@[expose, inline] def adjF (u v : N7) (bu bv : Nat) : Bool :=
  bF u v == 0 && fMul bu bv != fNorm (hF u v)

@[expose, inline] def b0F (c : N7) (b1 b2 b4 b5 b6 : Nat) : Nat :=
  fNeg (fAdd (fAdd (fAdd (fMul c.x1 b4) (fMul c.x2 b5)) (fAdd (fMul c.x4 b1) (fMul c.x5 b2)))
    (fMul 5 (fMul c.x6 b6)))

@[expose, inline] def vtxF (c : N7) (γ : Nat) (b : N7) (β : Nat) : Bool :=
  β != 0 && β != fNorm b.x0 && fMul γ β != fNorm (hF c b)

@[expose] def mkA (c : N7) (x2 x5 x6 : Nat) : N7 :=
  let b4 := fAdd (fNeg (fMul x2 x5)) (fMul x6 x6)
  ⟨b0F c 1 x2 b4 x5 x6, 1, x2, 0, b4, x5, x6⟩

@[expose] def mkB (c : N7) (x4 x6 : Nat) : N7 :=
  ⟨b0F c 0 1 x4 (fMul x6 x6) x6, 0, 1, 0, x4, fMul x6 x6, x6⟩

@[expose] def mkC (c : N7) (x5 : Nat) : N7 := ⟨b0F c 0 0 1 x5 0, 0, 0, 0, 1, x5, 0⟩

@[expose] def mkD (c : N7) : N7 := ⟨b0F c 0 0 0 1 0, 0, 0, 0, 0, 1, 0⟩

@[expose, inline] def sameVec (u v : N7) : Bool :=
  u.x0 == v.x0 && u.x1 == v.x1 && u.x2 == v.x2 && u.x3 == v.x3 && u.x4 == v.x4 && u.x5 == v.x5 &&
    u.x6 == v.x6

@[expose] def anyFrom (p : Nat → Bool) (i : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => p i || anyFrom p (i + 1) n

@[expose] def allFrom (p : Nat → Bool) (i : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => p i && allFrom p (i + 1) n

@[expose] def hubEntry (c : N7) (γ β2 : Nat) (r : N7) (βr i : Nat) : Bool × N7 × Nat :=
  let v := mkA c β2 (i / 49) (i % 49)
  let bv := hDiag v
  (vtxF c γ v bv && adjF v r bv βr, v, bv)

@[expose] def hubTable (c : N7) (γ β2 : Nat) (r : N7) (βr : Nat) : Array (Bool × N7 × Nat) :=
  Array.ofFn (n := 2401) fun i => hubEntry c γ β2 r βr i.val

@[expose] def hubTryH (hub : Array (Bool × N7 × Nat)) (di k0 ku6 : Nat) (u : N7) (bu t : Nat) :
    Bool :=
  let num := fAdd (fAdd (fMul u.x1 (fMul t t)) k0) (fMul ku6 t)
  let e := hub[fMul (fNeg num) di * 49 + t]!
  e.1 && adjF u e.2.1 bu e.2.2

@[expose] def hubNbr (hub : Array (Bool × N7 × Nat)) (β2 : Nat) (u : N7) (bu : Nat) : Bool :=
  anyFrom (hubTryH hub (fInv (fAdd u.x2 (fNeg (fMul β2 u.x1)))) (fAdd u.x4 (fMul β2 u.x5))
    (fMul 5 u.x6) u bu) 0 49

@[expose] def fbA (c : N7) (γ : Nat) (hub : Array (Bool × N7 × Nat)) (β2 k : Nat) :
    Option (N7 × Nat) :=
  let i := k * 117 % 117649
  let w := mkA c (i / 2401) (i / 49 % 49) (i % 49)
  let bw := hDiag w
  if vtxF c γ w bw && hubNbr hub β2 w bw then some (w, bw) else none

@[expose] def fbB (c : N7) (γ : Nat) (hub : Array (Bool × N7 × Nat)) (β2 k : Nat) :
    Option (N7 × Nat) :=
  let j := k * 3
  let w := mkB c (j / 49) (j % 49)
  let bw := hDiag w
  if vtxF c γ w bw && hubNbr hub β2 w bw then some (w, bw) else none

@[expose] def fallbackA (c : N7) (γ : Nat) (hub : Array (Bool × N7 × Nat)) (β2 : Nat) :
    List (N7 × Nat) :=
  (List.range 1700).filterMap (fbA c γ hub β2)

@[expose] def fallbackB (c : N7) (γ : Nat) (hub : Array (Bool × N7 × Nat)) (β2 : Nat) :
    List (N7 × Nat) :=
  (List.range 800).filterMap (fbB c γ hub β2)

@[expose] def reachOk (c : N7) (γ : Nat) (r : N7) (βr β2 : Nat) (hub : Array (Bool × N7 × Nat))
    (wl : List (N7 × Nat)) (u : N7) : Bool :=
  let bu := hDiag u
  !vtxF c γ u bu || sameVec u r || adjF u r bu βr || hubNbr hub β2 u bu ||
    wl.any fun p => adjF u p.1 bu p.2

@[expose, inline] def coordsLt (c : N7) : Bool :=
  c.x0 < 49 && c.x1 < 49 && c.x2 < 49 && c.x3 < 49 && c.x4 < 49 && c.x5 < 49 && c.x6 < 49

@[expose] def rootIdx (c : N7) (γ : Nat) : Option Nat :=
  (List.range 48).find? fun k => vtxF c γ (mkC c (k + 1)) (hDiag (mkC c (k + 1)))

@[expose] def rowLoops (c : N7) (γ : Nat) (r : N7) (βr β2 : Nat) (hub : Array (Bool × N7 × Nat))
    (wl : List (N7 × Nat)) : Bool :=
  let okU := reachOk c γ r βr β2 hub wl
  allFrom (fun x2 => allFrom (fun x5 => allFrom (fun x6 => okU (mkA c x2 x5 x6)) 0 49) 0 49)
      0 49 &&
    allFrom (fun x4 => allFrom (fun x6 => okU (mkB c x4 x6)) 0 49) 0 49 &&
    allFrom (fun x5 => okU (mkC c x5)) 0 49 && okU (mkD c)

@[expose] def rowCore (c : N7) (γ k : Nat) : Bool :=
  let r := mkC c (k + 1)
  let β2 := fNeg (fInv (k + 1))
  let hub := hubTable c γ β2 r (hDiag r)
  rowLoops c γ r (hDiag r) β2 hub (fallbackA c γ hub β2 ++ fallbackB c γ hub β2)

@[expose] def q7FastRow (row : Array Nat) : Bool :=
  let c := rowN row
  let γ := herN c c
  coordsLt c && c.x3 == 1 && isFFN c &&
    match rootIdx c γ with
    | none => false
    | some k => rowCore c γ k

@[expose] def q7FastCheck : Bool := q7RepsData.all q7FastRow

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
