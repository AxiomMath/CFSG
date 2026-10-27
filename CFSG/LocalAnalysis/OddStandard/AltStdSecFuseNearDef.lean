module

public import Mathlib.GroupTheory.PGroup
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseCnt
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv

@[expose] def nearSet (n : ℕ) (P : Subgroup (Perm (Fin n))) : Set (Perm (Fin n)) :=
  {1} ∪ {p | p ∈ P ∧ p * p = 1 ∧ p ≠ 1 ∧ 4 ≤ Nat.card (Function.fixedPoints p) ∧
    Perm.sign p = 1}

@[expose] noncomputable def nearTriple (n : ℕ) (P : Subgroup (Perm (Fin n))) (g : Perm (Fin n)) :
    ℕ := prodCnt (nearSet n P) g

@[expose] def NearCount12 : Prop :=
  ∀ P : Subgroup (Perm (Fin 12)), P ≤ alternatingGroup (Fin 12) → IsPGroup 2 P →
    (∀ P' : Subgroup (Perm (Fin 12)), P' ≤ alternatingGroup (Fin 12) → IsPGroup 2 P' → P ≤ P' →
      P' = P) →
    ∀ y ∈ P, y ∈ nearSet 12 P → y ≠ 1 → (∀ p ∈ P, p * y = y * p) →
      nearTriple 12 P 1 ≠ nearTriple 12 P y

end CFSG.OddStandard.AltStdSec
