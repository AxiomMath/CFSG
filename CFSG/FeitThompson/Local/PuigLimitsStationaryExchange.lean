module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration
import Mathlib.Data.SetLike.Fintype

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

theorem exists_puigSeries_two_mul_eq_puigLower (X : Type*) [Group X] [Finite X] :
    ∃ r : ℕ, ∀ n, r ≤ n → puigSeries X (2 * n) = puigLower X := by
  obtain ⟨r, hr⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun n => puigSeries X (2 * n), puigSeries_even_monotone⟩ : ℕ →o Subgroup X)
  simp only [OrderHom.coe_mk] at hr
  refine ⟨r, fun n hn => le_antisymm (le_puigLower n) ?_⟩
  rw [puigLower_eq_iSup]
  refine iSup_le fun m => ?_
  calc puigSeries X (2 * m) ≤ puigSeries X (2 * max m n) :=
        puigSeries_even_monotone (le_max_left m n)
    _ = puigSeries X (2 * n) := by
        rw [← hr (max m n) (hn.trans (le_max_right m n)), hr n hn]

theorem exists_puigSeries_two_mul_add_one_eq_puigUpper (X : Type*) [Group X] [Finite X] :
    ∃ r : ℕ, ∀ n, r ≤ n → puigSeries X (2 * n + 1) = puigUpper X := by
  obtain ⟨r, hr⟩ := WellFoundedLT.antitone_chain_condition
    (f := fun n : ℕ => puigSeries X (2 * n + 1)) puigSeries_odd_antitone
  refine ⟨r, fun n hn => le_antisymm ?_ (puigUpper_le n)⟩
  rw [puigUpper_eq_iInf]
  refine le_iInf fun m => ?_
  calc puigSeries X (2 * n + 1) = puigSeries X (2 * max m n + 1) := by
        rw [← hr (max m n) (hn.trans (le_max_right m n)), hr n hn]
    _ ≤ puigSeries X (2 * m + 1) := puigSeries_odd_antitone (le_max_left m n)

theorem exists_puigSeries_stationary (X : Type*) [Group X] [Finite X] :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ n, r ≤ n →
      puigSeries X (2 * n) = puigLower X ∧ puigSeries X (2 * n + 1) = puigUpper X := by
  obtain ⟨r, hr⟩ := exists_puigSeries_two_mul_eq_puigLower X
  obtain ⟨s, hs⟩ := exists_puigSeries_two_mul_add_one_eq_puigUpper X
  refine ⟨max r s + 1, le_add_self, fun n hn => ⟨hr n ?_, hs n ?_⟩⟩
  · exact ((le_max_left r s).trans (Nat.le_succ _)).trans hn
  · exact ((le_max_right r s).trans (Nat.le_succ _)).trans hn

theorem exists_puigSeries_two_mul_add_one_eq_puigSubgroup (X : Type*) [Group X] [Finite X] :
    ∃ r : ℕ, ∀ n, r ≤ n → puigSeries X (2 * n + 1) = puigSubgroup X := by
  simpa [puigSubgroup_eq_puigUpper] using exists_puigSeries_two_mul_add_one_eq_puigUpper X

theorem puigLambda_puigLower (X : Type*) [Group X] [Finite X] :
    puigLambda (puigLower X) = puigUpper X := by
  obtain ⟨r, -, hr⟩ := exists_puigSeries_stationary X
  obtain ⟨he, ho⟩ := hr r le_rfl
  rw [← ho, puigSeries_succ, he]

theorem puigLambda_puigUpper (X : Type*) [Group X] [Finite X] :
    puigLambda (puigUpper X) = puigLower X := by
  obtain ⟨r, -, hr⟩ := exists_puigSeries_stationary X
  have ho := (hr r le_rfl).2
  have he := (hr (r + 1) (Nat.le_succ r)).1
  rw [← he, show 2 * (r + 1) = 2 * r + 1 + 1 by ring, puigSeries_succ, ho]

theorem puigLambda_puigSubgroup (X : Type*) [Group X] [Finite X] :
    puigLambda (puigSubgroup X) = puigLower X := by
  rw [puigSubgroup_eq_puigUpper, puigLambda_puigUpper]

theorem puigLambda_puigLambda_puigUpper (X : Type*) [Group X] [Finite X] :
    puigLambda (puigLambda (puigUpper X)) = puigUpper X := by
  rw [puigLambda_puigUpper, puigLambda_puigLower]

theorem puigLambda_puigLambda_puigLower (X : Type*) [Group X] [Finite X] :
    puigLambda (puigLambda (puigLower X)) = puigLower X := by
  rw [puigLambda_puigLower, puigLambda_puigUpper]

end CFSG.FeitThompson

end
