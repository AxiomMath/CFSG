module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4M
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix

variable {F : Type} [Field F]

abbrev jJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks 0 1 (-1) 0

theorem mult_eq_neg_sq (h2 : (2 : F) ≠ 0) {A : GL (Fin 2 ⊕ Fin 2) F} {μ c : F}
    (hJ : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * jJ *
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = μ • jJ)
    (hll : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)
    (hP : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = c • 1)
    (hsq : ∃ l : F, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * A = l • 1)
    (hns : ∀ l : F, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1) :
    c ≠ 0 ∧ μ = -(c * c) := by
  obtain ⟨l, hl⟩ := hsq
  set M := (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hM
  have hPT := ul_transpose_mul_lr hll hJ
  rw [hP, transpose_smul, transpose_one, smul_mul, Matrix.one_mul] at hPT
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hPT
    have hμ : μ = 0 := by
      have := congrFun (congrFun hPT 0) 0
      simpa using this.symm
    rw [hμ, zero_smul] at hJ
    have hJ0 : (jJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 0 := by
      have hMA : M * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
          1 := by rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have e : (jJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
          ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F)ᵀ * (Mᵀ * jJ * M) *
            ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) := by
        calc (jJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
            = (M * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F))ᵀ * jJ *
                (M * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F)) := by
              rw [hMA, transpose_one, Matrix.one_mul, Matrix.mul_one]
          _ = _ := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      rw [e, hJ, Matrix.mul_zero, Matrix.zero_mul]
    have := congrFun (congrFun hJ0 (Sum.inl 0)) (Sum.inr 0)
    simp at this
  have hT : M.toBlocks₂₂ = (μ / c) • 1 := by
    have : M.toBlocks₂₂ = c⁻¹ • (c • M.toBlocks₂₂) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this, hPT, smul_smul, div_eq_inv_mul]
  have hA : M = fromBlocks (c • 1) M.toBlocks₁₂ 0 ((μ / c) • 1) := by
    rw [← hP, ← hll, ← hT, fromBlocks_toBlocks]
  have hsq2 := hl
  rw [hA, fromBlocks_multiply] at hsq2
  rw [show (l • 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks (l • 1) 0 0 (l • 1) by rw [← fromBlocks_one, fromBlocks_smul, smul_zero]]
    at hsq2
  rw [fromBlocks_inj] at hsq2
  obtain ⟨h11, h12, -, h22⟩ := hsq2
  simp only [smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul,
    add_zero, smul_smul, Matrix.mul_zero, zero_add] at h11 h12 h22
  have hl1 : c * c = l := by
    have := congrFun (congrFun h11 0) 0
    simpa using this
  have hl2 : μ / c * (μ / c) = l := by
    have := congrFun (congrFun h22 0) 0
    simpa using this
  refine ⟨hc, ?_⟩
  by_cases hμc : μ / c = c
  · exfalso
    have hQ : M.toBlocks₁₂ = 0 := by
      rw [hμc, ← add_smul] at h12
      have h2c : c + c ≠ 0 := by
        rw [← two_mul]
        exact mul_ne_zero h2 hc
      have := congrArg (fun X => (c + c)⁻¹ • X) h12
      simpa [smul_smul, inv_mul_cancel₀ h2c] using this
    apply hns c
    rw [hA, hQ, hμc, ← fromBlocks_one, fromBlocks_smul, smul_zero]
  · have h' : (μ / c - c) * (μ / c + c) = 0 := by linear_combination hl2 - hl1
    have hneg : μ / c + c = 0 := (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hμc)
    have : μ = (μ / c) * c := by field_simp
    rw [this, eq_neg_of_add_eq_zero_left hneg]
    ring

theorem false_of_three (h2 : (2 : F) ≠ 0) {A₁ A₂ : GL (Fin 2 ⊕ Fin 2) F} {μ₁ μ₂ c₁ c₂ : F}
    (hJ₁ : (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * jJ *
      (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = μ₁ • jJ)
    (hJ₂ : (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * jJ *
      (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = μ₂ • jJ)
    (hll₁ : (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)
    (hll₂ : (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)
    (hP₁ : (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = c₁ • 1)
    (hP₂ : (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = c₂ • 1)
    (hsq₁ : ∃ l : F, (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * A₁ = l • 1)
    (hsq₂ : ∃ l : F, (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * A₂ = l • 1)
    (hsq₁₂ : ∃ l : F,
      ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = l • 1)
    (hns₁ : ∀ l : F, (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1)
    (hns₂ : ∀ l : F, (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1)
    (hns₁₂ : ∀ l : F,
      ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1) :
    False := by
  obtain ⟨hc₁, hμ₁⟩ := mult_eq_neg_sq h2 hJ₁ hll₁ hP₁ hsq₁ hns₁
  obtain ⟨hc₂, hμ₂⟩ := mult_eq_neg_sq h2 hJ₂ hll₂ hP₂ hsq₂ hns₂
  have hJ₁₂ : ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      jJ * ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        (μ₁ * μ₂) • jJ := by
    calc ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
          jJ * ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
        = (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
            ((A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * jJ *
              (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) *
                (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
          rw [Units.val_mul, transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (μ₁ * μ₂) • jJ := by
          rw [hJ₁, Matrix.mul_smul, Matrix.smul_mul, hJ₂, smul_smul]
  have hll₁₂ := ll_mul hll₁ hll₂
  rw [← Units.val_mul] at hll₁₂
  have hP₁₂ : ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = (c₁ * c₂) • 1 := by
    rw [Units.val_mul, ul_mul hll₂, hP₁, hP₂, smul_mul, Matrix.one_mul, smul_smul]
  obtain ⟨-, hμ₁₂⟩ := mult_eq_neg_sq h2 hJ₁₂ hll₁₂ hP₁₂ hsq₁₂ hns₁₂
  rw [hμ₁, hμ₂] at hμ₁₂
  have h0 : 2 * ((c₁ * c₂) * (c₁ * c₂)) = 0 := by linear_combination hμ₁₂
  exact mul_ne_zero h2 (mul_ne_zero (mul_ne_zero hc₁ hc₂) (mul_ne_zero hc₁ hc₂)) h0

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
