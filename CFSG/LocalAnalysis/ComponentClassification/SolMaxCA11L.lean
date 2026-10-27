module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.SolMax

open Equiv

theorem support_mul_subset_of_swap_mul_swap {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ * σ = 1) {i i' : α} (hi : i ∈ σ.support) (hi' : i' ∈ σ.support)
    (hii' : i' ≠ i) (hσi' : i' ≠ σ i) :
    (swap i (σ i) * swap i' (σ i')).support ⊆ σ.support ∧
      (σ * (swap i (σ i) * swap i' (σ i'))).support ⊆
        σ.support \ (swap i (σ i) * swap i' (σ i')).support := by
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  have h1 : σ i ≠ i := Perm.mem_support.mp hi
  have h2 : σ i' ≠ i' := Perm.mem_support.mp hi'
  have h3 : σ i' ≠ i := fun h => hσi' (by rw [← h, hσσ])
  have h4 : σ i' ≠ σ i := fun h => hii' (σ.injective h)
  set δ := swap i (σ i) * swap i' (σ i') with hδdef
  have key : ∀ v, δ v ≠ v → δ v = σ v := by
    intro v hv
    rw [hδdef, Perm.mul_apply] at hv ⊢
    by_cases hv1 : v = i'
    · subst hv1
      rw [swap_apply_left, swap_apply_of_ne_of_ne h3 h4]
    by_cases hv2 : v = σ i'
    · subst hv2
      rw [swap_apply_right, swap_apply_of_ne_of_ne hii' hσi', hσσ]
    rw [swap_apply_of_ne_of_ne hv1 hv2] at hv ⊢
    by_cases hv3 : v = i
    · subst hv3
      rw [swap_apply_left]
    by_cases hv4 : v = σ i
    · subst hv4
      rw [swap_apply_right, hσσ]
    rw [swap_apply_of_ne_of_ne hv3 hv4] at hv
    exact absurd rfl hv
  have hsub : δ.support ⊆ σ.support := by
    intro v hv
    rw [Perm.mem_support] at hv ⊢
    rw [← key v hv]
    exact hv
  refine ⟨hsub, fun v hv => ?_⟩
  rw [Perm.mem_support, Perm.mul_apply] at hv
  rw [Finset.mem_sdiff, Perm.mem_support, Perm.mem_support]
  by_cases hδv : δ v = v
  · rw [hδv] at hv
    exact ⟨hv, not_not.mpr hδv⟩
  · rw [key v hδv, hσσ] at hv
    exact absurd rfl hv

theorem eq_one_of_card_support_le_three {α : Type*} [Fintype α] [DecidableEq α] {π : Perm α}
    (hπ : π * π = 1) (hA : π ∈ alternatingGroup α) (h3 : π.support.card ≤ 3) : π = 1 := by
  have h2 : 2 ∣ π.support.card := Perm.two_dvd_card_support (by rw [sq, hπ])
  have h02 : π.support.card = 0 ∨ π.support.card = 2 := by omega
  rcases h02 with h0 | h2'
  · exact Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0)
  · have hsign := (Perm.card_support_eq_two.mp h2').sign_eq
    rw [Perm.mem_alternatingGroup.mp hA] at hsign
    exact absurd hsign (by decide)

end CFSG.ComponentClassification.SolMax
