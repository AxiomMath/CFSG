module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.Fix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (monomGL)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem conjAut_proj_eq_of_smul (A : GL (Fin 3) F) (g : SL(3, F)) {c : Fˣ} (hc : c ^ 3 = 1)
    (h : (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (c : F) • (g : Matrix (Fin 3) (Fin 3) F)) :
    conjAut 3 F A (proj 3 F g) = proj 3 F g := by
  rw [conjAut_proj]
  apply proj_eq_of_val_eq_smul hc
  rw [coe_slConjugation]
  exact h

theorem fS_proj_eq_of_smul (σ : F ≃+* F) (g : SL(3, F)) {c : Fˣ} (hc : c ^ 3 = 1)
    (h : ∀ i j, σ ((g : Matrix (Fin 3) (Fin 3) F) i j) = c * (g : Matrix (Fin 3) (Fin 3) F) i j) :
    fS σ (proj 3 F g) = proj 3 F g := by
  change fieldAut 3 F σ (proj 3 F g) = _
  rw [fieldAut_proj]
  apply proj_eq_of_val_eq_smul hc
  ext i j
  simp [h]

theorem fS_proj_eq_proj_of_smul (σ : F ≃+* F) (g g' : SL(3, F)) {c : Fˣ} (hc : c ^ 3 = 1)
    (h : ∀ i j, σ ((g : Matrix (Fin 3) (Fin 3) F) i j) = c * (g' : Matrix (Fin 3) (Fin 3) F) i j) :
    fS σ (proj 3 F g) = proj 3 F g' := by
  change fieldAut 3 F σ (proj 3 F g) = _
  rw [fieldAut_proj]
  apply proj_eq_of_val_eq_smul hc
  ext i j
  simp [h]

variable [Finite F] {σ : F ≃+* F} {lam ω : Fˣ}

theorem mem_hyperFix_diag (h : HeisHyp σ lam ω) (A : SL(3, F))
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) F) i j = 0)
    (hσA : ∀ i, σ ((A : Matrix (Fin 3) (Fin 3) F) i i) = (A : Matrix (Fin 3) (Fin 3) F) i i) :
    proj 3 F A ∈ hyperFix σ lam ω := by
  refine mem_hyperFix_of_fS_cD h (fS_proj_eq_of_fixed σ A fun i j => ?_) (cD_proj_diag ω A hA)
  by_cases hij : i = j
  · subst hij; exact hσA i
  · rw [hA i j hij, map_zero]

@[expose] noncomputable def permSL : SL(3, F) :=
  ⟨(monomGL F 1 : Matrix (Fin 3) (Fin 3) F), by
    simp [monomGL, Matrix.det_fin_three]⟩

theorem coe_permSL :
    ((permSL : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  simp [permSL, monomGL]

theorem mem_hyperFix_perm (h : HeisHyp σ lam ω) : proj 3 F permSL ∈ hyperFix σ lam ω := by
  refine mem_hyperFix_of_fS_cD h (fS_proj_eq_of_fixed σ _ fun i j => ?_) ?_
  · rw [coe_permSL]
    fin_cases i <;> fin_cases j <;> simp
  · change conjAut 3 F (Dω ω) _ = _
    have h3 : (ω : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h.ω3, Units.val_one]
    have hω0 : (ω : F) ≠ 0 := ω.ne_zero
    refine conjAut_proj_eq_of_smul _ _ h.ω3 ?_
    rw [coe_permSL, Dω, CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL, Matrix.mul_apply,
        Fin.sum_univ_three]
    all_goals (try field_simp)
    all_goals first | rfl | ring1 | exact h3.symm | exact h3 | linear_combination (-1) * h3 |
      linear_combination h3

@[expose] noncomputable def polyXSL (lam : Fˣ) (α : F) (μ : Fˣ)
    (hμ : (μ : F) ^ 3 * (α ^ 3 + lam) = 1) : SL(3, F) :=
  ⟨(μ : F) • (α • 1 + (monomGL F lam : Matrix (Fin 3) (Fin 3) F)), by
    rw [Matrix.det_smul, Fintype.card_fin, ← hμ]
    congr 1
    simp [monomGL, Matrix.det_fin_three]
    ring⟩

theorem coe_polyXSL (lam : Fˣ) (α : F) (μ : Fˣ) (hμ : (μ : F) ^ 3 * (α ^ 3 + lam) = 1) :
    ((polyXSL lam α μ hμ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (μ : F) • (α • 1 + (monomGL F lam : Matrix (Fin 3) (Fin 3) F)) := rfl

theorem ratio_pow_three {μ : Fˣ} (hμ : σ ((μ : F) ^ 3) = (μ : F) ^ 3) :
    (Units.map (σ : F →* F) μ * μ⁻¹) ^ 3 = 1 := by
  apply Units.ext
  have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
    Units.val_inv_eq_inv_val, Units.val_one, mul_pow, inv_pow]
  rw [← map_pow, hμ, mul_inv_cancel₀ (pow_ne_zero 3 hμ0)]

theorem mem_hyperFix_polyX (h : HeisHyp σ lam ω) {α : F} (hα : σ α = α) (μ : Fˣ)
    (hμ : (μ : F) ^ 3 * (α ^ 3 + lam) = 1) :
    proj 3 F (polyXSL lam α μ hμ) ∈ hyperFix σ lam ω := by
  have hμ3 : σ ((μ : F) ^ 3) = (μ : F) ^ 3 := by
    have hne : (α ^ 3 + (lam : F)) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hμ; exact zero_ne_one hμ
    have : (μ : F) ^ 3 = (α ^ 3 + lam)⁻¹ := eq_inv_of_mul_eq_one_left hμ
    rw [this, map_inv₀, map_add, map_pow, hα, h.fixl]
  refine mem_hyperFix_of_fS_cX h ?_ ?_
  · refine fS_proj_eq_of_smul σ _ (ratio_pow_three hμ3) fun i j => ?_
    rw [coe_polyXSL]
    have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val]
    fin_cases i <;> fin_cases j <;>
      simp [monomGL, hα, h.fixl] <;> field_simp
  · change conjAut 3 F (monomGL F lam) _ = _
    refine conjAut_proj_eq_of_smul _ _ (one_pow 3) ?_
    have hcomm : (monomGL F lam : Matrix (Fin 3) (Fin 3) F) *
        ((polyXSL lam α μ hμ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        ((polyXSL lam α μ hμ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
          (monomGL F lam : Matrix (Fin 3) (Fin 3) F) := by
      rw [coe_polyXSL, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hcomm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
      Units.val_one, one_smul]

@[expose] noncomputable def twistSL (σ : F ≃+* F) (a μ : Fˣ)
    (hμ : (μ : F) ^ 3 * ((a : F) * σ a * σ (σ a)) = 1) : SL(3, F) :=
  ⟨Matrix.diagonal ![(μ : F) * a, μ * σ a, μ * σ (σ a)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three, ← hμ]
    simp
    ring⟩

theorem coe_twistSL (σ : F ≃+* F) (a μ : Fˣ) (hμ : (μ : F) ^ 3 * ((a : F) * σ a * σ (σ a)) = 1) :
    ((twistSL σ a μ hμ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(μ : F) * a, μ * σ a, μ * σ (σ a)] := rfl

@[expose] noncomputable def cycSL (σ : F ≃+* F) (a μ : Fˣ)
    (hμ : (μ : F) ^ 3 * (σ (σ a) * a * σ a) = 1) : SL(3, F) :=
  ⟨Matrix.diagonal ![(μ : F) * σ (σ a), μ * a, μ * σ a], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three, ← hμ]
    simp
    ring⟩

theorem coe_cycSL (σ : F ≃+* F) (a μ : Fˣ) (hμ : (μ : F) ^ 3 * (σ (σ a) * a * σ a) = 1) :
    ((cycSL σ a μ hμ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(μ : F) * σ (σ a), μ * a, μ * σ a] := rfl

theorem monomGL_inv_val (lam : Fˣ) :
    (((monomGL F lam)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 1, 0; 0, 0, 1; ((lam⁻¹ : Fˣ) : F), 0, 0] := by
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [monomGL, Matrix.mul_apply, Fin.sum_univ_three]

theorem cX_proj_twistSL (σ : F ≃+* F) (a μ : Fˣ) (hμ : (μ : F) ^ 3 * ((a : F) * σ a * σ (σ a)) = 1)
    (hμ' : (μ : F) ^ 3 * (σ (σ a) * a * σ a) = 1) :
    cX lam (proj 3 F (twistSL σ a μ hμ)) = proj 3 F (cycSL σ a μ hμ') := by
  change conjAut 3 F (monomGL F lam) _ = _
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  change _ = (cycSL σ a μ hμ' : Matrix (Fin 3) (Fin 3) F)
  rw [coe_slConjugation, coe_twistSL, coe_cycSL, monomGL_inv_val]
  have hl0 : (lam : F) ≠ 0 := lam.ne_zero
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [monomGL]
  all_goals (try field_simp)

theorem mem_hyperFix_twisted (h : HeisHyp σ lam ω) (a μ : Fˣ)
    (hμ : (μ : F) ^ 3 * ((a : F) * σ a * σ (σ a)) = 1) :
    proj 3 F (twistSL σ a μ hμ) ∈ hyperFix σ lam ω := by
  have hσ3 : ∀ y : F, σ (σ (σ y)) = y := by
    intro y
    have := congrArg (fun τ : F ≃+* F => τ y) h.pow3
    simpa [pow_succ] using this
  have hμ3 : σ ((μ : F) ^ 3) = (μ : F) ^ 3 := by
    have hne : ((a : F) * σ a * σ (σ a)) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hμ; exact zero_ne_one hμ
    have : (μ : F) ^ 3 = ((a : F) * σ a * σ (σ a))⁻¹ := eq_inv_of_mul_eq_one_left hμ
    rw [this, map_inv₀, map_mul, map_mul, hσ3]
    ring_nf
  refine mem_hyperFix_of_cD_fScX h ?_ ?_
  · refine cD_proj_diag ω _ fun i j hij => ?_
    rw [coe_twistSL]
    exact Matrix.diagonal_apply_ne _ hij
  ·
    have hμ' : (μ : F) ^ 3 * (σ (σ a) * a * σ a) = 1 := by rw [← hμ]; ring
    rw [MulAut.mul_apply, cX_proj_twistSL σ a μ hμ hμ']
    refine fS_proj_eq_proj_of_smul σ _ _ (ratio_pow_three hμ3) fun i j => ?_
    have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
    rw [coe_twistSL, coe_cycSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, hσ3, Units.val_inv_eq_inv_val] <;> field_simp

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis
