module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K]

@[expose] def descentFixer (σ : K ≃+* K) : Subgroup (K ≃+* K) where
  carrier := {τ | ∀ a ∈ descentField σ, τ a = a}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {τ τ'} hτ hτ' a ha => by
    change τ (τ' a) = a
    rw [hτ' a ha, hτ a ha]
  inv_mem' := fun {τ} hτ a ha => by
    change τ.symm a = a
    rw [RingEquiv.symm_apply_eq, hτ a ha]

theorem mem_descentFixer {σ τ : K ≃+* K} : τ ∈ descentFixer σ ↔ ∀ a ∈ descentField σ, τ a = a :=
  Iff.rfl

theorem eq_one_or_eq_of_mem_zpowers {σ τ : K ≃+* K} (hσσ : σ * σ = 1)
    (hτ : τ ∈ Subgroup.zpowers σ) : τ = 1 ∨ τ = σ := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
  have hinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  clear hτ
  induction j using Int.induction_on with
  | zero => exact Or.inl (zpow_zero σ)
  | succ i ih =>
    rw [zpow_add_one]
    rcases ih with h | h
    · rw [h, one_mul]
      exact Or.inr rfl
    · rw [h, hσσ]
      exact Or.inl rfl
  | pred i ih =>
    rw [zpow_sub_one, hinv]
    rcases ih with h | h
    · rw [h, one_mul]
      exact Or.inr rfl
    · rw [h, hσσ]
      exact Or.inl rfl

variable [Finite K]

theorem card_descentField {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K}
    (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Even f ∧ Nat.card (descentField σ) = 2 ^ (f / 2) ∧
      ∀ φ : K ≃+* K, (∀ a ∈ descentField σ, φ a = a) → φ = 1 ∨ φ = σ := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ1
  have hfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (fun _ _ h => RingEquiv.ext (congrFun h))
  obtain ⟨hdvd, S₁, hS₁, hcard₁⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hord] at hdvd hcard₁
  have hmem₁ : ∀ a, a ∈ S₁ ↔ a ∈ descentField σ := by
    intro a
    rw [← SetLike.mem_coe, hS₁, Set.mem_ofPred_eq, mem_descentField]
    constructor
    · intro h
      exact h σ (Subgroup.mem_zpowers σ)
    · intro h τ hτ
      rcases eq_one_or_eq_of_mem_zpowers hσσ hτ with rfl | rfl
      · rfl
      · exact h
  have hk : Nat.card (descentField σ) = 2 ^ (f / 2) := by
    rw [← hcard₁]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => (hmem₁ a).symm)
  refine ⟨even_iff_two_dvd.mpr hdvd, hk, fun φ hφ => ?_⟩
  have hσB : σ ∈ descentFixer σ := fun a ha => mem_descentField.mp ha
  obtain ⟨hdvdB, S₂, hS₂, hcard₂⟩ := hA (descentFixer σ)
  have hmem₂ : ∀ a, a ∈ S₂ ↔ a ∈ descentField σ := by
    intro a
    rw [← SetLike.mem_coe, hS₂, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact mem_descentField.mpr (h σ hσB)
    · intro h τ hτ
      exact hτ a h
  have hcardB : Nat.card (descentFixer σ) = 2 := by
    have h1 : 2 ^ (f / Nat.card (descentFixer σ)) = 2 ^ (f / 2) := by
      rw [← hcard₂, ← hk]
      exact Nat.card_congr (Equiv.subtypeEquivRight hmem₂)
    have h2 : f / Nat.card (descentFixer σ) = f / 2 :=
      Nat.pow_right_injective (le_refl 2) h1
    have hBpos : 0 < Nat.card (descentFixer σ) := Nat.card_pos
    obtain ⟨m, hm⟩ := hdvdB
    obtain ⟨m', hm'⟩ := hdvd
    have hdivB : f / Nat.card (descentFixer σ) = m := by
      rw [hm, Nat.mul_div_cancel_left m hBpos]
    have hdiv2 : f / 2 = m' := by
      rw [hm', Nat.mul_div_cancel_left m' two_pos]
    have hmm : m = m' := by
      rw [← hdivB, ← hdiv2, h2]
    subst hmm
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm'
        omega
      · exact h
    exact Nat.eq_of_mul_eq_mul_right hm0 (hm.symm.trans hm')
  have hle : Subgroup.zpowers σ ≤ descentFixer σ := Subgroup.zpowers_le.mpr hσB
  have heq : Subgroup.zpowers σ = descentFixer σ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardB, Nat.card_zpowers, hord])
  exact eq_one_or_eq_of_mem_zpowers hσσ (heq ▸ hφ)

end CFSG.ComponentClassification.UnbalancedCatalog
