module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.Adapters.SpecialLinearPerfect
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.LinearGroups

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem special_linear_dimension_two_perfect (hK : ∃ s : Finset K, s.card = 4) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨l, hl⟩ := field_scalar_with_nontrivial_square hK
  refine ⟨SL2.commutator_eq_top l.ne_zero ?_⟩
  intro h
  apply hl
  apply Units.ext
  simpa using h

theorem special_linear_dimension_at_least_three_perfect (hn : 3 ≤ n) :
    Group.IsPerfect (SpecialLinearGroup (Fin n) K) :=
  CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hn

theorem special_linear_isPerfect (hn : 2 ≤ n) (h : 3 ≤ n ∨ ∃ s : Finset K, s.card = 4) :
    Group.IsPerfect (SpecialLinearGroup (Fin n) K) := by
  rcases h with h3 | h4
  · exact special_linear_dimension_at_least_three_perfect h3
  · rcases Nat.lt_or_ge n 3 with hlt | h3
    · obtain rfl : n = 2 := by omega
      exact special_linear_dimension_two_perfect h4
    · exact special_linear_dimension_at_least_three_perfect h3

theorem linear_projective_perfect (hn : 2 ≤ n) (h : 3 ≤ n ∨ ∃ s : Finset K, s.card = 4) :
    Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have := special_linear_isPerfect hn h
  infer_instance

theorem linear_projective_nontrivial (hn : 2 ≤ n) :
    Nontrivial (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  infer_instance

end CFSG.LinearGroups
