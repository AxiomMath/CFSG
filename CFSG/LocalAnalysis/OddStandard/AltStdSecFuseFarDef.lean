module

public import Mathlib.GroupTheory.PGroup
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseCnt
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv

@[expose] def farSet (n : ℕ) (P : Subgroup (Perm (Fin n))) : Set (Perm (Fin n)) :=
  {1} ∪ {p | p ∈ P ∧ p * p = 1 ∧ p ≠ 1 ∧ Nat.card (Function.fixedPoints p) ≤ 3 ∧
    Perm.sign p = 1}

@[expose] noncomputable def farTriple (n : ℕ) (P : Subgroup (Perm (Fin n))) (g : Perm (Fin n)) :
    ℕ := prodCnt (farSet n P) g

@[expose] def FarCount (n : ℕ) : Prop :=
  ∀ P : Subgroup (Perm (Fin n)), P ≤ alternatingGroup (Fin n) → IsPGroup 2 P →
    (∀ P' : Subgroup (Perm (Fin n)), P' ≤ alternatingGroup (Fin n) → IsPGroup 2 P' → P ≤ P' →
      P' = P) →
    ∀ y ∈ P, y ∈ farSet n P → y ≠ 1 → (∀ p ∈ P, p * y = y * p) →
      farTriple n P 1 ≠ farTriple n P y

end CFSG.OddStandard.AltStdSec
