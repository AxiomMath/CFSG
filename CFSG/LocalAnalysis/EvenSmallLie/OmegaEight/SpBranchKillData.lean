module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchOrbit

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

variable (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ) (N : ℕ)

@[expose] def kInv : List ℕ := (List.range N).filter fun c => mul c c == 0 && c != 0

@[expose] def kOrd4 : List ℕ :=
  (List.range N).filter fun c => mul c c != 0 && mul (mul c c) (mul c c) == 0

@[expose] def kRec (m u : ℕ) : List (ℕ × ℕ) := orbitRec mul inv gens m u

@[expose] def kRecGood (m u : ℕ) : Bool :=
  orbOK mul inv N u (kRec mul inv gens m u) &&
    (orbClosed mul inv gens u (kRec mul inv gens m u) || decide (m < (kRec mul inv gens m u).length))

@[expose] def kCount (L : List ℕ) (u : ℕ) : ℕ := (L.filter fun x => mul x u == mul u x).length

@[expose] def kX (I O R : List ℕ) (ti : ℕ × ℕ) : List ℕ :=
  R.filter fun u => kCount mul I u == ti.1 && kCount mul O u == ti.2

@[expose] def chiOK (b : List Bool) (χ : Array Bool) : Bool :=
  χ.size == N && !χ[0]! && (List.range N).all fun c => (List.range gens.length).all fun j =>
    χ[mul c (gens.getD j 0)]! == (χ[c]! ^^ b.getD j false)

@[expose] def killAt (I O R : List ℕ) (m : ℕ) (χ : Array Bool) (n5 : Bool) (t : ℕ)
    (ti : ℕ × ℕ) : Bool :=
  orbClosed mul inv gens t (kRec mul inv gens m t) && (kRec mul inv gens m t).length == m &&
    orbOK mul inv N t (kRec mul inv gens m t) &&
    kCount mul I t == ti.1 && kCount mul O t == ti.2 && χ[t]! &&
    (if n5 then (kX mul I O R ti).all fun r => (kRec mul inv gens m t).any fun p => p.1 == r
      else (kX mul I O R ti).all fun r => χ[r]!)

end CFSG.EvenSmallLie.OmegaEight.SpBranch
