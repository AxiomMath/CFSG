module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4B

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup BS4 BL4

variable {K : Type} [Field K] {φ : K →+* K}

structure IsLinB (φ : K →+* K) (B : MB K) : Prop where
  bl : B.toBlocks₂₁ = 0
  herm : (B.map φ)ᵀ * jU * B = jU
  sq : ∃ s : K, B * B = s • 1
  ns : ∀ μ : K, B ≠ μ • 1

theorem jU_ne_zero : (jU : MB K) ≠ 0 := by
  intro h
  have := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
  simp at this

theorem caseLU (h2 : (2 : K) ≠ 0) {H : Subgroup (GL (Fin 2 ⊕ Fin 2) K)}
    (hH21 : ∀ x ∈ H, (x : MB K).toBlocks₂₁ = 0)
    (hHu : ∀ x ∈ H, ((x : MB K).map φ)ᵀ * jU * (x : MB K) = jU) {B₁ B₂ : MB K} {μ : K}
    (hB₁ : IsLinB φ B₁) (hB₂ : IsLinB φ B₂) (hB₃ : IsLinB φ (μ • (B₁ * B₂)))
    (hB₁H : ∀ x ∈ H, B₁ * (x : MB K) = (x : MB K) * B₁)
    (hB₂H : ∀ x ∈ H, B₂ * (x : MB K) = (x : MB K) * B₂) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  by_cases hc₁ : ∃ c : K, B₁.toBlocks₁₁ = c • 1
  swap
  · push Not at hc₁
    exact comm_of_herm_blocks hB₁.bl hc₁ hH21 hB₁H hHu
  by_cases hc₂ : ∃ c : K, B₂.toBlocks₁₁ = c • 1
  swap
  · push Not at hc₂
    exact comm_of_herm_blocks hB₂.bl hc₂ hH21 hB₂H hHu
  exfalso
  obtain ⟨c₁, hc₁⟩ := hc₁
  obtain ⟨c₂, hc₂⟩ := hc₂
  obtain ⟨s₁, hs₁⟩ := hB₁.sq
  obtain ⟨s₂, hs₂⟩ := hB₂.sq
  obtain ⟨s₃, hs₃⟩ := hB₃.sq
  have n₁ := norm_neg_one hB₁.bl hB₁.herm hc₁ hs₁ hB₁.ns
  have n₂ := norm_neg_one hB₂.bl hB₂.herm hc₂ hs₂ hB₂.ns
  have hc₃ : (μ • (B₁ * B₂)).toBlocks₁₁ = (μ * c₁ * c₂) • 1 := by
    have e : (μ • (B₁ * B₂)).toBlocks₁₁ = μ • (B₁ * B₂).toBlocks₁₁ := rfl
    rw [e, ul_mul hB₂.bl, hc₁, hc₂, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      smul_smul, smul_smul]
  have n₃ := norm_neg_one hB₃.bl hB₃.herm hc₃ hs₃ hB₃.ns
  have hμ := norm_one_of_smul jU_ne_zero (herm_mul hB₁.herm hB₂.herm) hB₃.herm
  rw [map_mul, map_mul] at n₃
  exact h2 (by linear_combination n₃ - (c₁ * φ c₁) * (c₂ * φ c₂) * hμ - (c₂ * φ c₂) * n₁ + n₂)

theorem caseGU (h2 : (2 : K) ≠ 0) {H : Subgroup (GL (Fin 2 ⊕ Fin 2) K)}
    (hH21 : ∀ x ∈ H, (x : MB K).toBlocks₂₁ = 0)
    (hHu : ∀ x ∈ H, ((x : MB K).map φ)ᵀ * jU * (x : MB K) = jU) {B A : MB K}
    (hB : IsLinB φ B) (hBH : ∀ x ∈ H, B * (x : MB K) = (x : MB K) * B)
    (hA21 : A.toBlocks₂₁ = 0) (hAd : A.det ≠ 0) (hBA : B * A * B.map φ = A) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  by_cases hc : ∃ c : K, B.toBlocks₁₁ = c • 1
  swap
  · push Not at hc
    exact comm_of_herm_blocks hB.bl hc hH21 hBH hHu
  exfalso
  obtain ⟨c, hc⟩ := hc
  obtain ⟨s, hs⟩ := hB.sq
  have n₁ := norm_neg_one hB.bl hB.herm hc hs hB.ns
  have n₂ := norm_one_of_semi hB.bl hc hA21 hAd hBA
  exact h2 (by linear_combination n₁ - n₂)

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
