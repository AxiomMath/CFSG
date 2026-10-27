module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.FiveCount
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Five

open Module QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem eq_one_of_ne_zero [Finite K] (hK : Nat.card K = 2) {a : K} (ha : a ≠ 0) : a = 1 := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  exact (hy a ha).trans (hy 1 one_ne_zero).symm

theorem two_eq_zero [Finite K] (hK : Nat.card K = 2) : (2 : K) = 0 := by
  by_contra h
  have h1 := eq_one_of_ne_zero hK h
  exact one_ne_zero (by linear_combination h1 : (1 : K) = 0)

theorem forall_mem_span_eq_zero {Q : QuadraticForm K V} {s : Set V} (hQ : ∀ x ∈ s, Q x = 0)
    (hB : ∀ x ∈ s, ∀ y ∈ s, polar Q x y = 0) : ∀ x ∈ Submodule.span K s, Q x = 0 := by
  have h1 : ∀ x ∈ Submodule.span K s, ∀ y ∈ s, polar Q x y = 0 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem z hz => exact hB z hz y hy
    | zero => exact polar_zero_left Q y
    | add a b _ _ ha hb => rw [polar_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [polar_smul_left, ha, smul_zero]
  have h2 : ∀ x ∈ Submodule.span K s, ∀ y ∈ Submodule.span K s, polar Q x y = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h1 x hx z hz
    | zero => exact polar_zero_right Q x
    | add a b _ _ ha hb => rw [polar_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [polar_smul_right, ha, smul_zero]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz => exact hQ z hz
  | zero => exact Q.map_zero
  | add a b ha' hb' ha hb =>
    have h := h2 a ha' b hb'
    rw [polar, ha, hb, sub_zero, sub_zero] at h
    exact h
  | smul c a _ ha => rw [QuadraticMap.map_smul, ha, smul_zero]

theorem polar_eq_zero_of_forall {Q : QuadraticForm K V} {U : Submodule K V}
    (hU : ∀ x ∈ U, Q x = 0) {x y : V} (hx : x ∈ U) (hy : y ∈ U) : polar Q x y = 0 := by
  rw [polar, hU _ (U.add_mem hx hy), hU x hx, hU y hy, sub_zero, sub_zero]

theorem exists_ne_zero_eq_zero_of_three_le [Finite K] (hK : Nat.card K = 2)
    (Q : QuadraticForm K V) {U : Submodule K V} [FiniteDimensional K U]
    (hU : 3 ≤ finrank K U) : ∃ u ∈ U, u ≠ 0 ∧ Q u = 0 := by
  by_contra hcon
  have h1 : ∀ u ∈ U, u ≠ 0 → Q u = 1 := fun u hu h0 =>
    eq_one_of_ne_zero hK fun hQ => hcon ⟨u, hu, h0, hQ⟩
  have hU0 : U ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hU
    omega
  obtain ⟨a, haU, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have haU' : K ∙ a ≤ U := (Submodule.span_singleton_le_iff_mem a U).mpr haU
  have hlt1 : K ∙ a < U := by
    refine lt_of_le_of_ne haU' fun h => ?_
    have := finrank_span_singleton (K := K) ha0
    rw [h] at this
    omega
  obtain ⟨b, hbU, hba⟩ := IsConcreteLE.exists_of_lt hlt1
  have hb0 : b ≠ 0 := fun h => hba (h ▸ Submodule.zero_mem _)
  have hbU' : K ∙ b ≤ U := (Submodule.span_singleton_le_iff_mem b U).mpr hbU
  have hlt2 : K ∙ a ⊔ K ∙ b < U := by
    refine lt_of_le_of_ne (sup_le haU' hbU') fun h => ?_
    have := Submodule.finrank_add_le_finrank_add_finrank (K ∙ a) (K ∙ b)
    rw [h, finrank_span_singleton ha0, finrank_span_singleton hb0] at this
    omega
  obtain ⟨c, hcU, hcab⟩ := IsConcreteLE.exists_of_lt hlt2
  have ham : a ∈ K ∙ a ⊔ K ∙ b := Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)
  have hbm : b ∈ K ∙ a ⊔ K ∙ b := Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)
  have hc0 : c ≠ 0 := fun h => hcab (h ▸ Submodule.zero_mem _)
  have hab0 : a + b ≠ 0 := fun h => hba (by
    rw [eq_neg_of_add_eq_zero_right h]
    exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self a))
  have hbc0 : b + c ≠ 0 := fun h => hcab (by
    rw [eq_neg_of_add_eq_zero_right h]
    exact Submodule.neg_mem _ hbm)
  have hca0 : c + a ≠ 0 := fun h => hcab (by
    rw [eq_neg_of_add_eq_zero_left h]
    exact Submodule.neg_mem _ ham)
  have habc0 : a + b + c ≠ 0 := fun h => hcab (by
    rw [eq_neg_of_add_eq_zero_right h]
    exact Submodule.neg_mem _ (Submodule.add_mem _ ham hbm))
  have key := QuadraticMap.map_add_add_add_map Q a b c
  rw [h1 _ (U.add_mem (U.add_mem haU hbU) hcU) habc0, h1 a haU ha0, h1 b hbU hb0, h1 c hcU hc0,
    h1 _ (U.add_mem haU hbU) hab0, h1 _ (U.add_mem hbU hcU) hbc0,
    h1 _ (U.add_mem hcU haU) hca0] at key
  exact one_ne_zero (by linear_combination key : (1 : K) = 0)

variable {Q : QuadraticForm K V} {φ : V ≃ₗ[K] V}

theorem map_pow_apply (hφQ : ∀ x, Q (φ x) = Q x) (n : ℕ) (x : V) : Q ((φ ^ n) x) = Q x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, hφQ, ih]

theorem polar_pow_apply (hφQ : ∀ x, Q (φ x) = Q x) (n : ℕ) (x y : V) :
    polar Q ((φ ^ n) x) ((φ ^ n) y) = polar Q x y := by
  rw [polar, polar, ← map_add, map_pow_apply hφQ, map_pow_apply hφQ, map_pow_apply hφQ]

theorem polar_normSum (hφQ : ∀ x, Q (φ x) = Q x) (h2 : (2 : K) = 0) {c : V}
    (hc : c ∈ fixedSpace φ) (x : V) : polar Q c (normSum φ x) = polar Q c x := by
  have hpow : ∀ n, polar Q c ((φ ^ n) x) = polar Q c x := fun n => by
    conv_lhs => rw [← pow_apply_of_mem_fixedSpace hc n]
    exact polar_pow_apply hφQ n c x
  simp only [normSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, polar_add_right,
    hpow]
  linear_combination (2 * polar Q c x) * h2

end CFSG.AGLEmbedding.TrialityTwo.Five
