module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_iSup_lt_le_sum (A : ℕ → Submodule K V) (cost : ℕ → ℕ)
    (h : ∀ j, finrank K ↥(A j ⊔ ⨆ i < j, A i) ≤ finrank K ↥(⨆ i < j, A i) + cost j) (n : ℕ) :
    finrank K ↥(⨆ i < n, A i) ≤ ∑ j ∈ Finset.range n, cost j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.iSup_lt_succ A n, sup_comm, Finset.sum_range_succ]
    have hn := h n
    omega

theorem finrank_sup_le_add_two {A S : Submodule K V} (hA : finrank K A ≤ 2) :
    finrank K ↥(A ⊔ S) ≤ finrank K S + 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A S
  omega

theorem finrank_sup_le_add_one {A B S : Submodule K V} (hA : finrank K A ≤ 2) (hB : B ≤ S)
    (h : A ⊓ B ≠ ⊥) : finrank K ↥(A ⊔ S) ≤ finrank K S + 1 := by
  have hAB : finrank K ↥(A ⊓ B) ≤ finrank K ↥(A ⊓ S) :=
    Submodule.finrank_mono (inf_le_inf_left A hB)
  have hpos : 1 ≤ finrank K ↥(A ⊓ B) := Submodule.one_le_finrank_iff.mpr h
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq A S
  omega

omit [FiniteDimensional K V] in
theorem finrank_sup_le_of_le {A S : Submodule K V} (h : A ≤ S) :
    finrank K ↥(A ⊔ S) ≤ finrank K S + 0 := by
  rw [sup_eq_right.mpr h, add_zero]

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
