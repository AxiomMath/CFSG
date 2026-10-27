module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {X : Type*} [Group X] {A : Subgroup X}

theorem le_puigLambda_of_normal (hA : IsMulCommutative A) [A.Normal] (U : Subgroup X) :
    A ≤ puigLambda U :=
  le_puigLambda hA (by rw [normalizer_eq_top]; exact le_top)

theorem le_puigSeries_of_normal (hA : IsMulCommutative A) [A.Normal] {n : ℕ} (hn : 1 ≤ n) :
    A ≤ puigSeries X n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [puigSeries_succ]
  exact le_puigLambda_of_normal hA _

theorem le_puigLower_of_normal (hA : IsMulCommutative A) [A.Normal] : A ≤ puigLower X :=
  (le_puigSeries_of_normal hA (n := 2 * 1) (by omega)).trans (le_puigLower 1)

theorem puigLower_le_puigSubgroup : puigLower X ≤ puigSubgroup X := by
  rw [puigSubgroup_eq_puigUpper]; exact puigLower_le_puigUpper

theorem le_puigSubgroup_of_normal (hA : IsMulCommutative A) [A.Normal] : A ≤ puigSubgroup X :=
  (le_puigLower_of_normal hA).trans puigLower_le_puigSubgroup

theorem le_puigUpper_of_normal (hA : IsMulCommutative A) [A.Normal] : A ≤ puigUpper X :=
  (le_puigLower_of_normal hA).trans puigLower_le_puigUpper

end CFSG.FeitThompson

end
