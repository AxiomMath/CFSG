module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Retract

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open scoped commutatorElement Pointwise

variable {E : Type*} [Group E]

theorem mem_sup_iff_of_normalizes {Q A : Subgroup E} (hAQ : ∀ a ∈ A, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q)
    {g : E} : g ∈ Q ⊔ A ↔ ∃ q ∈ Q, ∃ a ∈ A, g = q * a := by
  have hnorm : A ≤ Subgroup.normalizer (Q : Set E) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hAQ a ha q hq, fun hq => ?_⟩
    have := hAQ a⁻¹ (A.inv_mem ha) _ hq
    rwa [inv_inv, show a⁻¹ * (a * q * a⁻¹) * a = q by group] at this
  have h := Subgroup.coe_mul_of_right_le_normalizer_left Q A hnorm
  have : g ∈ ((Q ⊔ A : Subgroup E) : Set E) ↔ g ∈ (Q : Set E) * (A : Set E) := by rw [h]
  constructor
  · intro hg
    obtain ⟨q, hq, a, ha, rfl⟩ := this.1 hg
    exact ⟨q, hq, a, ha, rfl⟩
  · rintro ⟨q, hq, a, ha, rfl⟩
    exact this.2 ⟨q, hq, a, ha, rfl⟩

theorem commutator_sup_inf_eq_bot_of_sieg {C Q A : Subgroup E}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAQ : ∀ a ∈ A, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q) {κ : E → E}
    (hmul : ∀ y ∈ Q, ∀ y' ∈ Q, κ (y * y') = κ y * κ y') (hκC : ∀ c ∈ C, κ c = c)
    (hκZ : ∀ y ∈ Q, κ y ∈ Subgroup.center E) (hκinv : ∀ a ∈ A, ∀ q ∈ Q, κ (a * q * a⁻¹) = κ q) :
    ⁅Q ⊔ A, Q ⊔ A⁆ ⊓ C = ⊥ := by
  have h1 : κ 1 = 1 := by simpa using hκC 1 C.one_mem
  have hinv : ∀ q ∈ Q, κ q⁻¹ = (κ q)⁻¹ := fun q hq => by
    have := hmul q hq q⁻¹ (Q.inv_mem hq)
    rw [mul_inv_cancel, h1] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hform : ∀ q₁ ∈ Q, ∀ a₁ ∈ A, ∀ q₂ ∈ Q, ∀ a₂ ∈ A,
      ⁅q₁ * a₁, q₂ * a₂⁆ = q₁ * (a₁ * q₂ * a₁⁻¹) * (a₂ * q₁⁻¹ * a₂⁻¹) * q₂⁻¹ := by
    intro q₁ _ a₁ ha₁ q₂ _ a₂ ha₂
    have hc : a₂ * a₁⁻¹ = a₁⁻¹ * a₂ := by
      have : a₁ * a₂ = a₂ * a₁ := hA a₁ ha₁ a₂ ha₂
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← this]
      group
    simp only [commutatorElement_def]
    calc q₁ * a₁ * (q₂ * a₂) * (q₁ * a₁)⁻¹ * (q₂ * a₂)⁻¹
        = q₁ * (a₁ * q₂ * (a₂ * a₁⁻¹)) * q₁⁻¹ * a₂⁻¹ * q₂⁻¹ := by group
      _ = q₁ * (a₁ * q₂ * (a₁⁻¹ * a₂)) * q₁⁻¹ * a₂⁻¹ * q₂⁻¹ := by rw [hc]
      _ = _ := by group
  have hmem : ∀ q₁ ∈ Q, ∀ a₁ ∈ A, ∀ q₂ ∈ Q, ∀ a₂ ∈ A,
      q₁ * (a₁ * q₂ * a₁⁻¹) * (a₂ * q₁⁻¹ * a₂⁻¹) * q₂⁻¹ ∈ Q := by
    intro q₁ hq₁ a₁ ha₁ q₂ hq₂ a₂ ha₂
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hq₁ (hAQ a₁ ha₁ q₂ hq₂))
      (hAQ a₂ ha₂ q₁⁻¹ (Q.inv_mem hq₁))) (Q.inv_mem hq₂)
  refine commutator_inf_eq_bot_of_fun (K := C) (Y := Q) (G := Q ⊔ A) ?_ hmul hκC ?_
  · intro g hg h hh
    obtain ⟨q₁, hq₁, a₁, ha₁, rfl⟩ := (mem_sup_iff_of_normalizes hAQ).1 hg
    obtain ⟨q₂, hq₂, a₂, ha₂, rfl⟩ := (mem_sup_iff_of_normalizes hAQ).1 hh
    rw [hform q₁ hq₁ a₁ ha₁ q₂ hq₂ a₂ ha₂]
    exact hmem q₁ hq₁ a₁ ha₁ q₂ hq₂ a₂ ha₂
  · intro g hg h hh
    obtain ⟨q₁, hq₁, a₁, ha₁, rfl⟩ := (mem_sup_iff_of_normalizes hAQ).1 hg
    obtain ⟨q₂, hq₂, a₂, ha₂, rfl⟩ := (mem_sup_iff_of_normalizes hAQ).1 hh
    rw [hform q₁ hq₁ a₁ ha₁ q₂ hq₂ a₂ ha₂]
    have e1 : a₁ * q₂ * a₁⁻¹ ∈ Q := hAQ a₁ ha₁ q₂ hq₂
    have e2 : a₂ * q₁⁻¹ * a₂⁻¹ ∈ Q := hAQ a₂ ha₂ q₁⁻¹ (Q.inv_mem hq₁)
    rw [hmul _ (Q.mul_mem (Q.mul_mem hq₁ e1) e2) _ (Q.inv_mem hq₂),
      hmul _ (Q.mul_mem hq₁ e1) _ e2, hmul _ hq₁ _ e1, hκinv a₁ ha₁ q₂ hq₂,
      hκinv a₂ ha₂ q₁⁻¹ (Q.inv_mem hq₁), hinv q₁ hq₁, hinv q₂ hq₂]
    have hc1 : κ q₁ * κ q₂ = κ q₂ * κ q₁ := Subgroup.mem_center_iff.1 (hκZ q₂ hq₂) (κ q₁)
    calc κ q₁ * κ q₂ * (κ q₁)⁻¹ * (κ q₂)⁻¹ = (κ q₂ * κ q₁) * (κ q₁)⁻¹ * (κ q₂)⁻¹ := by rw [hc1]
      _ = 1 := by group

end CFSG.ClassicalInvolution.ModelFacts.OddCover
