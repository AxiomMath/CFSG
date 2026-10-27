module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResA7

open Equiv Equiv.Perm Subgroup

theorem cycleType_of_involution_alt {σ : Perm (Fin 7)} (hσA : σ ∈ alternatingGroup (Fin 7))
    (hσ : orderOf σ = 2) : σ.cycleType = Multiset.replicate 2 2 := by
  have hall : ∀ m ∈ σ.cycleType, m = 2 := by
    intro m hm
    have h1 := dvd_of_mem_cycleType hm
    rw [hσ] at h1
    have h2 := two_le_of_mem_cycleType hm
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · omega
    · exact h
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum := sum_cycleType_le σ
  rw [hrep, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hsign := sign_of_cycleType σ
  rw [hrep, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    (Perm.mem_alternatingGroup).mp hσA] at hsign
  have hne : Multiset.card σ.cycleType ≠ 0 := by
    intro h0
    have : σ.cycleType = 0 := Multiset.card_eq_zero.mp h0
    rw [cycleType_eq_zero] at this
    rw [this, orderOf_one] at hσ
    omega
  have hhi : Multiset.card σ.cycleType ≤ 3 := by omega
  have hlo : 1 ≤ Multiset.card σ.cycleType := Nat.one_le_iff_ne_zero.mpr hne
  rw [hrep]
  congr 1
  interval_cases h : Multiset.card σ.cycleType
  · exact absurd hsign (by decide)
  · rfl
  · exact absurd hsign (by decide)

theorem klein_of_involution_alt {σ : Perm (Fin 7)} (hσA : σ ∈ alternatingGroup (Fin 7))
    (hσ : orderOf σ = 2) :
    ∃ τ ∈ alternatingGroup (Fin 7), ∃ c ∈ alternatingGroup (Fin 7), τ * τ = 1 ∧
      σ * τ = τ * σ ∧ τ ≠ σ ∧ c * σ * c⁻¹ = τ ∧ c * τ * c⁻¹ = σ * τ := by
  set σ₀ : Perm (Fin 7) := swap 0 1 * swap 2 3 with hσ₀
  set τ₀ : Perm (Fin 7) := swap 0 2 * swap 1 3 with hτ₀
  set c₀ : Perm (Fin 7) := swap 1 3 * swap 1 2 with hc₀
  have hmem : ∀ {a b c d : Fin 7}, a ≠ b → c ≠ d → swap a b * swap c d ∈ alternatingGroup (Fin 7) :=
    fun hab hcd => by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
      rfl
  have hσ₀A : σ₀ ∈ alternatingGroup (Fin 7) := hmem (by decide) (by decide)
  have hσ₀2 : orderOf σ₀ = 2 := orderOf_eq_prime (by decide) (by decide)
  have hct : σ₀.cycleType = σ.cycleType := by
    rw [cycleType_of_involution_alt hσ₀A hσ₀2, cycleType_of_involution_alt hσA hσ]
  have hsupp : σ₀.support.card + 2 ≤ Fintype.card (Fin 7) := by
    rw [← sum_cycleType, cycleType_of_involution_alt hσ₀A hσ₀2]
    decide
  obtain ⟨⟨g, hgA⟩, hg⟩ := isConj_iff.mp (alternatingGroup.isConj_of (σ := ⟨σ₀, hσ₀A⟩)
    (τ := ⟨σ, hσA⟩) (isConj_iff_cycleType_eq.mpr hct) hsupp)
  have hg' : g * σ₀ * g⁻¹ = σ := congrArg Subtype.val hg
  have hcA : g * c₀ * g⁻¹ ∈ alternatingGroup (Fin 7) :=
    mul_mem (mul_mem hgA (hmem (by decide) (by decide))) (inv_mem hgA)
  refine ⟨g * τ₀ * g⁻¹, mul_mem (mul_mem hgA (hmem (by decide) (by decide))) (inv_mem hgA),
    g * c₀ * g⁻¹, hcA, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show g * τ₀ * g⁻¹ * (g * τ₀ * g⁻¹) = g * (τ₀ * τ₀) * g⁻¹ by group,
      show τ₀ * τ₀ = 1 by decide]
    group
  · rw [← hg', show g * σ₀ * g⁻¹ * (g * τ₀ * g⁻¹) = g * (σ₀ * τ₀) * g⁻¹ by group,
      show g * τ₀ * g⁻¹ * (g * σ₀ * g⁻¹) = g * (τ₀ * σ₀) * g⁻¹ by group,
      show σ₀ * τ₀ = τ₀ * σ₀ by decide]
  · rw [← hg']
    intro h
    have : τ₀ = σ₀ := mul_left_cancel (mul_right_cancel h)
    exact absurd this (by decide)
  · rw [← hg', show g * c₀ * g⁻¹ * (g * σ₀ * g⁻¹) * (g * c₀ * g⁻¹)⁻¹ =
      g * (c₀ * σ₀ * c₀⁻¹) * g⁻¹ by group, show c₀ * σ₀ * c₀⁻¹ = τ₀ by decide]
  · rw [← hg', show g * c₀ * g⁻¹ * (g * τ₀ * g⁻¹) * (g * c₀ * g⁻¹)⁻¹ =
      g * (c₀ * τ₀ * c₀⁻¹) * g⁻¹ by group, show c₀ * τ₀ * c₀⁻¹ = σ₀ * τ₀ by decide]
    group

theorem klein_of_involution {Y : Type*} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) {y : Y}
    (hy : orderOf y = 2) :
    ∃ y' c : Y, y' * y' = 1 ∧ y * y' = y' * y ∧ y' ≠ y ∧ c * y * c⁻¹ = y' ∧
      c * y' * c⁻¹ = y * y' := by
  have hσ : orderOf ((e y : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
  obtain ⟨τ, hτA, c, hcA, h1, h2, h3, h4, h5⟩ := klein_of_involution_alt (e y).2 hσ
  have key : ∀ a b : Y, ((e a : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ((e b : alternatingGroup (Fin 7)) : Perm (Fin 7)) → a = b :=
    fun a b h => e.injective (Subtype.ext h)
  refine ⟨e.symm ⟨τ, hτA⟩, e.symm ⟨c, hcA⟩, key _ _ ?_, key _ _ ?_, fun h => h3 ?_,
    key _ _ ?_, key _ _ ?_⟩
  · simp only [map_mul, MulEquiv.apply_symm_apply, map_one, Subgroup.coe_mul,
      Subgroup.coe_one]
    exact h1
  · simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    exact h2
  · have := congrArg (fun x => ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
    simpa using this
  · simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact h4
  · simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact h5

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResA7
