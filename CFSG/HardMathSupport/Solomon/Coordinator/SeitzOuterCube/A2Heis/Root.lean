module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.Elements

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (monomGL)
open scoped MatrixGroups

variable {F : Type} [Field F]

section Matrices

variable (lam : Fˣ) (α γ : F)

noncomputable abbrev kc : F := (γ ^ 3 - 1) / (α ^ 3 + lam)

noncomputable abbrev matX : Matrix (Fin 3) (Fin 3) F :=
  !![1, -α * lam * kc lam α γ, -α * lam * kc lam α γ * α;
    0, 1 + lam * kc lam α γ, lam * kc lam α γ * α;
    0, α ^ 2 * kc lam α γ, 1 + α ^ 2 * kc lam α γ * α]

noncomputable abbrev nc : F := α * lam * (γ ^ 3 - 1) ^ 2 / ((α ^ 3 + lam) * γ ^ 6)

noncomputable abbrev matC : Matrix (Fin 3) (Fin 3) F :=
  !![1, nc lam α γ, nc lam α γ * α; 0, 1, 0; 0, 0, 1]

variable {lam α γ}

theorem matB_mul_matX (hΔ : α ^ 3 + (lam : F) ≠ 0) :
    (α • 1 + (monomGL F lam : Matrix (Fin 3) (Fin 3) F)) * matX lam α γ =
      Matrix.diagonal ![1, 1, γ ^ 3] * (α • 1 + (monomGL F lam : Matrix (Fin 3) (Fin 3) F)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [monomGL, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, kc] <;>
    field_simp <;> ring

theorem det_matX (hΔ : α ^ 3 + (lam : F) ≠ 0) : (matX lam α γ).det = γ ^ 3 := by
  rw [Matrix.det_fin_three]
  simp [kc]
  field_simp
  ring

theorem matC_mul_matX_mul_z (hΔ : α ^ 3 + (lam : F) ≠ 0) (hγ : γ ≠ 0) :
    matC lam α γ * matX lam α γ * Matrix.diagonal ![γ⁻¹ ^ 2, γ, γ] =
      Matrix.diagonal ![γ⁻¹ ^ 2, γ, γ] * matX lam α γ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, kc, nc] <;>
    field_simp <;> ring

theorem matT_mul_matC_mul_t (hΔ : α ^ 3 + (lam : F) ≠ 0) (hγ : γ ≠ 0) :
    (1 + Matrix.single 0 1 (nc lam α γ * (γ ^ 3 - 1))) * matC lam α γ *
        Matrix.diagonal ![γ, γ⁻¹ ^ 2, γ] =
      Matrix.diagonal ![γ, γ⁻¹ ^ 2, γ] * matC lam α γ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.single_apply,
      Matrix.one_apply, nc] <;>
    field_simp <;> ring

end Matrices

section Group

@[expose] noncomputable def diagSL (a b c : F) (h : a * b * c = 1) : SL(3, F) :=
  ⟨Matrix.diagonal ![a, b, c], by rw [Matrix.det_diagonal, Fin.prod_univ_three]; simpa using h⟩

theorem coe_diagSL (a b c : F) (h : a * b * c = 1) :
    ((diagSL a b c h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![a, b, c] := rfl

variable {lam : Fˣ} {α γ : F}

@[expose] noncomputable def xSL (lam : Fˣ) (α γ : F) (hΔ : α ^ 3 + (lam : F) ≠ 0) (hγ : γ ≠ 0) :
    SL(3, F) :=
  ⟨γ⁻¹ • matX lam α γ, by
    rw [Matrix.det_smul, det_matX hΔ, Fintype.card_fin, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 3 hγ)]⟩

@[expose] noncomputable def cSL (lam : Fˣ) (α γ : F) : SL(3, F) :=
  ⟨matC lam α γ, by rw [Matrix.det_fin_three]; simp⟩

theorem polyXSL_mul_xSL (hΔ : α ^ 3 + (lam : F) ≠ 0) (hγ : γ ≠ 0) (μ : Fˣ)
    (hμ : (μ : F) ^ 3 * (α ^ 3 + lam) = 1) :
    polyXSL lam α μ hμ * xSL lam α γ hΔ hγ =
      diagSL γ⁻¹ γ⁻¹ (γ ^ 2) (by field_simp) * polyXSL lam α μ hμ := by
  apply Subtype.ext
  change ((μ : F) • (α • 1 + (monomGL F lam : Matrix (Fin 3) (Fin 3) F))) * (γ⁻¹ • matX lam α γ) =
    Matrix.diagonal ![γ⁻¹, γ⁻¹, γ ^ 2] *
      ((μ : F) • (α • 1 + (monomGL F lam : Matrix (Fin 3) (Fin 3) F)))
  have hd : Matrix.diagonal ![γ⁻¹, γ⁻¹, γ ^ 2] = γ⁻¹ • Matrix.diagonal ![1, 1, γ ^ 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> field_simp
  rw [Matrix.smul_mul, Matrix.mul_smul, matB_mul_matX hΔ, hd, Matrix.smul_mul, Matrix.mul_smul,
    smul_comm]

theorem cSL_mul_xSL_mul_z (hΔ : α ^ 3 + (lam : F) ≠ 0) (hγ : γ ≠ 0) :
    cSL lam α γ * xSL lam α γ hΔ hγ * diagSL (γ⁻¹ ^ 2) γ γ (by field_simp) =
      diagSL (γ⁻¹ ^ 2) γ γ (by field_simp) * xSL lam α γ hΔ hγ := by
  apply Subtype.ext
  change matC lam α γ * (γ⁻¹ • matX lam α γ) * Matrix.diagonal ![γ⁻¹ ^ 2, γ, γ] =
    Matrix.diagonal ![γ⁻¹ ^ 2, γ, γ] * (γ⁻¹ • matX lam α γ)
  rw [Matrix.mul_smul, Matrix.smul_mul, matC_mul_matX_mul_z hΔ hγ, Matrix.mul_smul]

theorem transvection_mul_cSL_mul_t (hΔ : α ^ 3 + (lam : F) ≠ 0) (hγ : γ ≠ 0) :
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide)
        (nc lam α γ * (γ ^ 3 - 1)) * cSL lam α γ * diagSL γ (γ⁻¹ ^ 2) γ (by field_simp) =
      diagSL γ (γ⁻¹ ^ 2) γ (by field_simp) * cSL lam α γ := by
  apply Subtype.ext
  change (1 + Matrix.single 0 1 (nc lam α γ * (γ ^ 3 - 1))) * matC lam α γ *
      Matrix.diagonal ![γ, γ⁻¹ ^ 2, γ] = Matrix.diagonal ![γ, γ⁻¹ ^ 2, γ] * matC lam α γ
  exact matT_mul_matC_mul_t hΔ hγ

variable [Finite F] {σ : F ≃+* F} {ω : Fˣ}

theorem mem_hyperFix_diagSL (h : HeisHyp σ lam ω) {a b c : F} (hab : a * b * c = 1)
    (ha : σ a = a) (hb : σ b = b) (hc : σ c = c) :
    proj 3 F (diagSL a b c hab) ∈ hyperFix σ lam ω := by
  refine mem_hyperFix_diag h _ (fun i j hij => ?_) (fun i => ?_)
  · rw [coe_diagSL]; exact Matrix.diagonal_apply_ne _ hij
  · rw [coe_diagSL, Matrix.diagonal_apply_eq]
    fin_cases i <;> simp [ha, hb, hc]

theorem tbar_mem_closure_hyperFix (h : HeisHyp σ lam ω) (hα : σ α = α) (hγσ : σ γ = γ)
    (hγ : γ ≠ 0) (hΔ : α ^ 3 + (lam : F) ≠ 0) (μ : Fˣ) (hμ : (μ : F) ^ 3 * (α ^ 3 + lam) = 1) :
    CFSG.HardMathSupport.Foote.ModuleExclusions.tbar (show (0 : Fin 3) ≠ 1 by decide)
        (nc lam α γ * (γ ^ 3 - 1)) ∈ Subgroup.closure (hyperFix σ lam ω) := by
  set M := Subgroup.closure (hyperFix σ lam ω)
  have hγi : σ γ⁻¹ = γ⁻¹ := by rw [map_inv₀, hγσ]
  have hB := Subgroup.subset_closure (mem_hyperFix_polyX h hα μ hμ)
  have hs := Subgroup.subset_closure (mem_hyperFix_diagSL h (a := γ⁻¹) (b := γ⁻¹) (c := γ ^ 2)
    (by field_simp) hγi hγi (by rw [map_pow, hγσ]))
  have hz := Subgroup.subset_closure (mem_hyperFix_diagSL h (a := γ⁻¹ ^ 2) (b := γ) (c := γ)
    (by field_simp) (by rw [map_pow, hγi]) hγσ hγσ)
  have ht := Subgroup.subset_closure (mem_hyperFix_diagSL h (a := γ) (b := γ⁻¹ ^ 2) (c := γ)
    (by field_simp) hγσ (by rw [map_pow, hγi]) hγσ)
  have hx : xSL lam α γ hΔ hγ = (polyXSL lam α μ hμ)⁻¹ * diagSL γ⁻¹ γ⁻¹ (γ ^ 2) (by field_simp) *
      polyXSL lam α μ hμ := by
    rw [mul_assoc, eq_inv_mul_iff_mul_eq, polyXSL_mul_xSL hΔ hγ μ hμ]
  have hC : cSL lam α γ = diagSL (γ⁻¹ ^ 2) γ γ (by field_simp) * xSL lam α γ hΔ hγ *
      (diagSL (γ⁻¹ ^ 2) γ γ (by field_simp))⁻¹ * (xSL lam α γ hΔ hγ)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, cSL_mul_xSL_mul_z hΔ hγ]
  have hT : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide)
      (nc lam α γ * (γ ^ 3 - 1)) = diagSL γ (γ⁻¹ ^ 2) γ (by field_simp) * cSL lam α γ *
        (diagSL γ (γ⁻¹ ^ 2) γ (by field_simp))⁻¹ * (cSL lam α γ)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, transvection_mul_cSL_mul_t hΔ hγ]
  have hxM : proj 3 F (xSL lam α γ hΔ hγ) ∈ M := by
    rw [hx, map_mul, map_mul, map_inv]
    exact M.mul_mem (M.mul_mem (M.inv_mem hB) hs) hB
  have hCM : proj 3 F (cSL lam α γ) ∈ M := by
    rw [hC, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact M.mul_mem (M.mul_mem (M.mul_mem hz hxM) (M.inv_mem hz)) (M.inv_mem hxM)
  unfold CFSG.HardMathSupport.Foote.ModuleExclusions.tbar
  rw [hT, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact M.mul_mem (M.mul_mem (M.mul_mem ht hCM) (M.inv_mem ht)) (M.inv_mem hCM)

theorem nc_mul_ne_zero (hα0 : α ≠ 0) (hγ : γ ≠ 0) (hΔ : α ^ 3 + (lam : F) ≠ 0)
    (hγ3 : γ ^ 3 ≠ 1) : nc lam α γ * (γ ^ 3 - 1) ≠ 0 := by
  have hl : (lam : F) ≠ 0 := lam.ne_zero
  have h1 : γ ^ 3 - 1 ≠ 0 := sub_ne_zero.2 hγ3
  unfold nc
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero hα0 hl) (pow_ne_zero 2 h1))
    (mul_ne_zero hΔ (pow_ne_zero 6 hγ))) h1

end Group

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis
