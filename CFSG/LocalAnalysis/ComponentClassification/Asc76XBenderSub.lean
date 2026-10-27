module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XInputs

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem map_subtype_smul_sylow {M : Subgroup Q} {p : ℕ} (S : Sylow p M) (g : M) :
    ((g • S : Sylow p M) : Subgroup M).map M.subtype =
      rightConjugate ((S : Subgroup M).map M.subtype) (g : Q)⁻¹ := by
  ext x
  rw [mem_rightConjugate_iff, inv_inv, Sylow.coe_subgroup_smul]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨z, hz, hzx⟩
    have hxM : x ∈ M := by
      have h1 : (g : Q)⁻¹ * x * g ∈ M := hzx ▸ z.2
      have : x = (g : Q) * ((g : Q)⁻¹ * x * g) * (g : Q)⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem g.2 h1) (inv_mem g.2)
    refine ⟨⟨x, hxM⟩, ⟨z, hz, ?_⟩, rfl⟩
    change MulAut.conj g z = ⟨x, hxM⟩
    apply Subtype.ext
    rw [MulAut.conj_apply]
    simp only [coe_mul, coe_inv]
    rw [show (z : Q) = (g : Q)⁻¹ * x * g from hzx]
    group

theorem BenderFacts.inf_eq_bot_of_isSylowOf (hB : BenderFacts) {M P₁ P₂ : Subgroup Q}
    (hM : IsSzOrU3 M) (h₁ : IsSylowOf 2 P₁ M) (h₂ : IsSylowOf 2 P₂ M) (hne : P₁ ≠ P₂) :
    P₁ ⊓ P₂ = ⊥ := by
  obtain ⟨S₁, rfl⟩ := h₁
  obtain ⟨S₂, rfl⟩ := h₂
  have hne' : S₁ ≠ S₂ := fun h => hne (h ▸ rfl)
  rw [← map_inf_eq _ _ _ M.subtype_injective, hB.sylow_inf M hM S₁ S₂ hne', Subgroup.map_bot]

theorem BenderFacts.exists_conj_of_isSylowOf (hB : BenderFacts) {M P₁ P₂ : Subgroup Q}
    (hM : IsSzOrU3 M) (h₁ : IsSylowOf 2 P₁ M) (h₂ : IsSylowOf 2 P₂ M) (hne : P₁ ≠ P₂) :
    ∃ x ∈ P₁ ⊔ P₂, P₂ = rightConjugate P₁ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁, rfl⟩ := h₁
  obtain ⟨S₂, rfl⟩ := h₂
  have hne' : S₁ ≠ S₂ := fun h => hne (h ▸ rfl)
  have hinf := hB.sylow_inf M hM S₂ S₁ (Ne.symm hne')
  have hS₂ : (S₂ : Subgroup M) ≠ ⊥ := by
    intro h
    apply hne'
    have h1 : Nat.card (S₂ : Subgroup M) = 1 := by rw [h, card_bot]
    have h2 : Nat.card (S₁ : Subgroup M) = 1 := by
      rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S₂, h1]
    apply Sylow.ext
    rw [Subgroup.card_eq_one.mp h1, Subgroup.card_eq_one.mp h2]
  obtain ⟨⟨q, hq⟩, hq1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS₂
  have hq1 : q ≠ 1 := fun h => hq1' (Subtype.ext h)
  have hqN : q ∉ normalizer ((S₁ : Subgroup M) : Set M) := by
    intro h
    have hmem : q ∈ (S₂ : Subgroup M) ⊓ normalizer ((S₁ : Subgroup M) : Set M) := ⟨hq, h⟩
    have h4 := IsPGroup.inf_normalizer_sylow S₂.isPGroup' S₁
    have h5 : q ∈ (S₂ : Subgroup M) ⊓ (S₁ : Subgroup M) := h4.le hmem
    rw [hinf, mem_bot] at h5
    exact hq1 h5
  have h1 : q • S₁ ≠ S₁ := fun h => hqN (Sylow.smul_eq_iff_mem_normalizer.mp h)
  have h2 : q • S₁ ≠ S₂ := by
    intro h
    apply hne'
    have h3 : q • S₂ = S₂ := Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer hq)
    rw [← h3] at h
    exact smul_left_cancel q h
  obtain ⟨r, hr, hrS⟩ := hB.sylow_transitive M hM S₁ (q • S₁) S₂ h1 (Ne.symm hne')
  rw [← mul_smul] at hrS
  refine ⟨((r * q : M) : Q)⁻¹, ?_, ?_⟩
  · have hr' : (r : Q) ∈ (S₁ : Subgroup M).map M.subtype := ⟨r, hr, rfl⟩
    have hq' : (q : Q) ∈ (S₂ : Subgroup M).map M.subtype := ⟨q, hq, rfl⟩
    simp only [coe_mul, mul_inv_rev]
    exact mul_mem (inv_mem (mem_sup_right hq')) (inv_mem (mem_sup_left hr'))
  · rw [← hrS, map_subtype_smul_sylow]

end CFSG.ComponentClassification.Asc76X
