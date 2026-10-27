module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.KC.Misc.Cover

open Equiv

theorem cover_of_closed {G : Type*} [Group G] [Finite G] (gs : List G) (K : Subgroup G)
    (t : ℕ → G) (nT : ℕ) (hnT : 0 < nT) (ht0 : t 0 = 1)
    (hcl : ∀ j < nT, ∀ a ∈ gs, ∃ j' < nT, t j * a * (t j')⁻¹ ∈ K) :
    ∀ g ∈ Subgroup.closure {g | g ∈ gs}, ∃ j < nT, g * (t j)⁻¹ ∈ K := by
  intro g hg
  have hg' : g ∈ Submonoid.closure {g | g ∈ gs} := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  induction hg' using Submonoid.closure_induction_right with
  | one => exact ⟨0, hnT, by rw [ht0, inv_one, one_mul]; exact K.one_mem⟩
  | mul_right x _ a ha ih =>
    obtain ⟨j, hj, hk⟩ := ih
    obtain ⟨j', hj', hk'⟩ := hcl j hj a ha
    refine ⟨j', hj', ?_⟩
    have : x * a * (t j')⁻¹ = (x * (t j)⁻¹) * (t j * a * (t j')⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [this]
    exact K.mul_mem hk hk'

theorem mem_of_fix {n : ℕ} (gs : List (Perm (Fin n))) (K : Subgroup (Perm (Fin n)))
    (t : ℕ → Perm (Fin n)) (nT : ℕ) (hnT : 0 < nT) (ht0 : t 0 = 1) (x₀ : Fin n)
    (hK : ∀ k ∈ K, k x₀ = x₀) (hfix : ∀ j < nT, 0 < j → t j x₀ ≠ x₀)
    (hcl : ∀ j < nT, ∀ a ∈ gs, ∃ j' < nT, t j * a * (t j')⁻¹ ∈ K) :
    ∀ g ∈ Subgroup.closure {g | g ∈ gs}, g x₀ = x₀ → g ∈ K := by
  intro g hg hx
  obtain ⟨j, hj, hk⟩ := cover_of_closed gs K t nT hnT ht0 hcl g hg
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rwa [ht0, inv_one, mul_one] at hk
  · exfalso
    apply hfix j hj hj0
    have h1 := hK _ (K.inv_mem hk)
    have hgi : g⁻¹ x₀ = x₀ := by rw [Perm.inv_eq_iff_eq]; exact hx.symm
    rw [mul_inv_rev, inv_inv, Perm.mul_apply, hgi] at h1
    exact h1

end CFSG.KC.Misc.Cover

end
