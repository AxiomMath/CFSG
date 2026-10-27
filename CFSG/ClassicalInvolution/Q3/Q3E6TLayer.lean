module

public import CFSG.ClassicalInvolution.Q3.Q3TWWLayer
public import CFSG.ClassicalInvolution.Models.TwistedPairs.Unitary

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.WeakCT.SU4
  CFSG.ClassicalInvolution.Q3.Q3TW CFSG.ClassicalInvolution.Q3.Q3Z CFSG.Timmesfeld
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Criterion

variable {E : Type} [Field E] (θ : E →+* E) (hθ : ∀ c, θ (θ c) = c)

theorem unitaryJInv_mul : (unitaryJInv : Matrix (Fin 4) (Fin 4) E) * unitaryJ = 1 :=
  mul_eq_one_comm.mp unitaryJ_mul

theorem mem_unitaryGroup_of_mat (g : SL(4, E))
    (h : ((g : Matrix (Fin 4) (Fin 4) E).map θ)ᵀ * unitaryJInv * (g : Matrix (Fin 4) (Fin 4) E) =
      unitaryJInv) : g ∈ unitaryGroup θ hθ := by
  rw [mem_unitaryGroup]
  refine Subtype.ext ?_
  have e1 : ((sigmaA (involEquiv θ hθ) g : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) =
      unitaryJ * (((fieldAutSL (involEquiv θ hθ) 4 g)⁻¹ : SL(4, E)) :
        Matrix (Fin 4) (Fin 4) E)ᵀ * unitaryJInv := rfl
  rw [e1]
  set N := fieldAutSL (involEquiv θ hθ) 4 g with hN
  have hNm : (N : Matrix (Fin 4) (Fin 4) E) = (g : Matrix (Fin 4) (Fin 4) E).map θ := rfl
  have h1 : (((N⁻¹ : SL(4, E)) : Matrix (Fin 4) (Fin 4) E))ᵀ * (N : Matrix (Fin 4) (Fin 4) E)ᵀ
      = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    simp
  have h2 : (N : Matrix (Fin 4) (Fin 4) E)ᵀ * (unitaryJInv * (g : Matrix (Fin 4) (Fin 4) E) *
      unitaryJ) = 1 := by
    have h' : (N : Matrix (Fin 4) (Fin 4) E)ᵀ * (unitaryJInv * (g : Matrix (Fin 4) (Fin 4) E)) =
        unitaryJInv := by
      rw [hNm]
      simpa only [Matrix.mul_assoc] using h
    calc (N : Matrix (Fin 4) (Fin 4) E)ᵀ * (unitaryJInv * (g : Matrix (Fin 4) (Fin 4) E) *
          unitaryJ)
        = (N : Matrix (Fin 4) (Fin 4) E)ᵀ * (unitaryJInv * (g : Matrix (Fin 4) (Fin 4) E)) *
          unitaryJ := (Matrix.mul_assoc _ _ _).symm
      _ = unitaryJInv * unitaryJ := by rw [h']
      _ = 1 := unitaryJInv_mul
  have h3 := left_inv_eq_right_inv h1 h2
  rw [h3]
  generalize (g : Matrix (Fin 4) (Fin 4) E) = M
  calc unitaryJ * (unitaryJInv * M * unitaryJ) * unitaryJInv
      = (unitaryJ * unitaryJInv) * M * (unitaryJ * unitaryJInv) := by
        simp only [Matrix.mul_assoc]
    _ = M := by rw [unitaryJ_mul]; simp

end Criterion

section Diagonal

variable {E : Type} [Field E] (θ : E →+* E) (ι : E)

@[expose] def diagU : Matrix (Fin 4) (Fin 4) E := Matrix.diagonal ![1, 1, -ι, ι]

@[expose] def diagUInv : Matrix (Fin 4) (Fin 4) E := Matrix.diagonal ![1, 1, ι, -ι]

variable {ι}

theorem diagU_mul (hι : ι ^ 2 = -1) : diagU ι * diagUInv ι = (1 : Matrix (Fin 4) (Fin 4) E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagU, diagUInv, Matrix.mul_apply, Matrix.diagonal_apply]
  all_goals linear_combination (-1 : E) * hι

theorem diagUInv_mul (hι : ι ^ 2 = -1) :
    diagUInv ι * diagU ι = (1 : Matrix (Fin 4) (Fin 4) E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagU, diagUInv, Matrix.mul_apply, Matrix.diagonal_apply]
  all_goals linear_combination (-1 : E) * hι

theorem det_diagU (hι : ι ^ 2 = -1) : (diagU ι).det = 1 := by
  simp [diagU, Matrix.det_diagonal, Fin.prod_univ_four]
  linear_combination (-1 : E) * hι

theorem det_diagUInv (hι : ι ^ 2 = -1) : (diagUInv ι).det = 1 := by
  simp [diagUInv, Matrix.det_diagonal, Fin.prod_univ_four]
  linear_combination (-1 : E) * hι

theorem diagU_map (hθι : θ ι = -ι) : (diagU ι).map θ = diagUInv ι := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagU, diagUInv, hθι]

theorem diagUInv_map (hθι : θ ι = -ι) : (diagUInv ι).map θ = diagU ι := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagU, diagUInv, hθι]

theorem diagU_Q :
    diagU ι * unitaryJInv * diagUInv ι = (-ι) • (antidiag 4 : Matrix (Fin 4) (Fin 4) E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagU, diagUInv, unitaryJInv, antidiag, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.rev]

theorem diagUInv_J :
    diagUInv ι * antidiag 4 * diagU ι = ι • (unitaryJInv : Matrix (Fin 4) (Fin 4) E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagU, diagUInv, unitaryJInv, antidiag, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.diagonal_apply, Fin.rev]

theorem unitary_conj_mat (hι : ι ^ 2 = -1) (hθι : θ ι = -ι) (A : Matrix (Fin 4) (Fin 4) E)
    (hA : (A.map θ)ᵀ * antidiag 4 * A = antidiag 4) :
    ((diagUInv ι * A * diagU ι).map θ)ᵀ * unitaryJInv * (diagUInv ι * A * diagU ι) =
      unitaryJInv := by
  have hDt : (diagU ι)ᵀ = diagU ι := Matrix.diagonal_transpose _
  have hDit : (diagUInv ι)ᵀ = diagUInv ι := Matrix.diagonal_transpose _
  rw [Matrix.map_mul, Matrix.map_mul, diagU_map θ hθι, diagUInv_map θ hθι,
    Matrix.transpose_mul, Matrix.transpose_mul, hDt, hDit]
  have key : ∀ X Y : Matrix (Fin 4) (Fin 4) E,
      diagUInv ι * (X * diagU ι) * unitaryJInv * (diagUInv ι * Y * diagU ι) =
        diagUInv ι * (X * (diagU ι * unitaryJInv * diagUInv ι) * Y) * diagU ι := by
    intro X Y
    simp only [Matrix.mul_assoc]
  rw [key _ A, diagU_Q]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hA, diagUInv_J, smul_smul]
  have h1 : -ι * ι = 1 := by linear_combination (-1 : E) * hι
  rw [h1, one_smul]

end Diagonal

section Hom

variable {E : Type} [Field E] (θ : E →+* E) (hθ : ∀ c, θ (θ c) = c) {ι : E}
  (hι : ι ^ 2 = -1)

@[expose] noncomputable def toSLU : SU (involEquiv θ hθ) 4 →* SL(4, E) where
  toFun g := ⟨diagUInv ι * suMat (involEquiv θ hθ) g * diagU ι, by
    rw [Matrix.det_mul, Matrix.det_mul, det_diagUInv hι, det_diagU hι, one_mul, mul_one]
    exact (mem_SU.mp g.2).1⟩
  map_one' := by
    refine Subtype.ext ?_
    show diagUInv ι * suMat (involEquiv θ hθ) 1 * diagU ι = 1
    rw [map_one, Matrix.mul_one, diagUInv_mul hι]
  map_mul' g h := by
    refine Subtype.ext ?_
    show diagUInv ι * suMat (involEquiv θ hθ) (g * h) * diagU ι =
      (diagUInv ι * suMat (involEquiv θ hθ) g * diagU ι) *
        (diagUInv ι * suMat (involEquiv θ hθ) h * diagU ι)
    rw [map_mul]
    calc diagUInv ι * (suMat (involEquiv θ hθ) g * suMat (involEquiv θ hθ) h) * diagU ι
        = diagUInv ι * suMat (involEquiv θ hθ) g * (diagU ι * diagUInv ι) *
          suMat (involEquiv θ hθ) h * diagU ι := by
          rw [diagU_mul hι, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem coe_toSLU (g : SU (involEquiv θ hθ) 4) :
    ((toSLU θ hθ hι g : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) =
      diagUInv ι * suMat (involEquiv θ hθ) g * diagU ι := rfl

theorem toSLU_mem (hθι : θ ι = -ι) (g : SU (involEquiv θ hθ) 4) :
    toSLU θ hθ hι g ∈ unitaryGroup θ hθ := by
  refine mem_unitaryGroup_of_mat θ hθ _ ?_
  rw [coe_toSLU]
  exact unitary_conj_mat θ hι hθι _ (mem_SU.mp g.2).2

@[expose] noncomputable def toU (hθι : θ ι = -ι) : SU (involEquiv θ hθ) 4 →* unitaryGroup θ hθ :=
  (toSLU θ hθ hι).codRestrict (unitaryGroup θ hθ) (toSLU_mem θ hθ hι hθι)

end Hom

section Facts

variable {E : Type} [Field E] [CharP E 3] (θ : E →+* E) (hθ : ∀ c, θ (θ c) = c)
  (hθ3 : ∀ x, θ x = x ^ 3) {ι : E} (hι : ι ^ 2 = -1)

theorem hθι_of (hθ3 : ∀ x, θ x = x ^ 3) (hι : ι ^ 2 = -1) : θ ι = -ι := by
  rw [hθ3]
  linear_combination ι * hι

theorem autXp_coe : ((autXp : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
    !![1, 1; 0, 1] := rfl

theorem autXm_coe : ((autXm : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
    !![1, 0; 1, 1] := rfl

variable (e : ZMod 3 ≃+* fixedField θ)

theorem toU_letter2 :
    toU θ hθ hι (hθι_of θ hθ3 hι) (suLetter (involEquiv θ hθ) hθ3 hθ ι hι 2) =
      ulb θ hθ ((Matrix.SpecialLinearGroup.map e.toRingHom :
        SL(2, ZMod 3) →* SL(2, fixedField θ)) autXp) := by
  refine Subtype.ext (Subtype.ext ?_)
  show diagUInv ι * suMat (involEquiv θ hθ) (suLetter (involEquiv θ hθ) hθ3 hθ ι hι 2) *
    diagU ι = ((blockSL E 4 2 1 (by omega) (liftSL θ 2 ((Matrix.SpecialLinearGroup.map
      e.toRingHom : SL(2, ZMod 3) →* SL(2, fixedField θ)) autXp)) : SL(4, E)) :
      Matrix (Fin 4) (Fin 4) E)
  rw [coe_blockSL_four_one]
  have hs : suMat (involEquiv θ hθ) (suLetter (involEquiv θ hθ) hθ3 hθ ι hι 2) =
      longRootMatrix 1 ι := rfl
  rw [hs]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diagUInv, diagU, longRootMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.single_apply, Fin.rev, coe_liftSL, autXp_coe]
  all_goals linear_combination (-1 : E) * hι

theorem toU_letter3 :
    toU θ hθ hι (hθι_of θ hθ3 hι) (suLetter (involEquiv θ hθ) hθ3 hθ ι hι 3) =
      ulb θ hθ ((Matrix.SpecialLinearGroup.map e.toRingHom :
        SL(2, ZMod 3) →* SL(2, fixedField θ)) autXm) := by
  refine Subtype.ext (Subtype.ext ?_)
  show diagUInv ι * suMat (involEquiv θ hθ) (suLetter (involEquiv θ hθ) hθ3 hθ ι hι 3) *
    diagU ι = ((blockSL E 4 2 1 (by omega) (liftSL θ 2 ((Matrix.SpecialLinearGroup.map
      e.toRingHom : SL(2, ZMod 3) →* SL(2, fixedField θ)) autXm)) : SL(4, E)) :
      Matrix (Fin 4) (Fin 4) E)
  rw [coe_blockSL_four_one]
  have hs : suMat (involEquiv θ hθ) (suLetter (involEquiv θ hθ) hθ3 hθ ι hι 3) =
      longRootMatrix 2 (-ι) := rfl
  rw [hs]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diagUInv, diagU, longRootMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.single_apply, Fin.rev, coe_liftSL, autXm_coe]
  all_goals linear_combination (-1 : E) * hι

theorem toU_suroot01 (c : E) :
    toU θ hθ hι (hθι_of θ hθ3 hι) (suroot (involEquiv θ hθ) hθ 0 1 (by decide) (by decide)
      (by decide) c) = usb θ hθ (tv 0 1 c) := by
  refine Subtype.ext (Subtype.ext ?_)
  show diagUInv ι * rootMatrix (involEquiv θ hθ) 0 1 c * diagU ι =
    ((usbSL θ hθ (tv 0 1 c) : SL(4, E)) : Matrix (Fin 4) (Fin 4) E)
  rw [coe_usbSL, LevisExtras.tv01_eq_sl2Upper]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diagUInv, diagU, rootMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.single_apply, Fin.rev, involEquiv_apply,
      CFSG.LieType.Steinberg.sl2Upper, hθ3]
  all_goals first | linear_combination (-1 : E) * hι | linear_combination (-(c ^ 3)) * hι

theorem toU_suroot10 (c : E) :
    toU θ hθ hι (hθι_of θ hθ3 hι) (suroot (involEquiv θ hθ) hθ 1 0 (by decide) (by decide)
      (by decide) c) = usb θ hθ (tv 1 0 c) := by
  refine Subtype.ext (Subtype.ext ?_)
  show diagUInv ι * rootMatrix (involEquiv θ hθ) 1 0 c * diagU ι =
    ((usbSL θ hθ (tv 1 0 c) : SL(4, E)) : Matrix (Fin 4) (Fin 4) E)
  rw [coe_usbSL, LevisExtras.tv10_eq_sl2Lower]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diagUInv, diagU, rootMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.single_apply, Fin.rev, involEquiv_apply,
      CFSG.LieType.Steinberg.sl2Lower, hθ3]
  all_goals first | linear_combination (-1 : E) * hι | linear_combination (-(c ^ 3)) * hι

end Facts

section Transport

variable {K : Type} [Field K] [CharP K 3] (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 3)
  (hσσ : ∀ c, σ (σ c) = c) (ι : K) (hι : ι ^ 2 = -1)

theorem exists_twistedLayer_of_hom {H : Type} [Group H] (φ : SU σ 4 →* H)
    (lbZ : SL(2, ZMod 3) →* H) (sb : SL(2, K) →* H)
    (hlbp : φ (suLetter σ hσ hσσ ι hι 2) = lbZ autXp)
    (hlbm : φ (suLetter σ hσ hσσ ι hι 3) = lbZ autXm)
    (hsb01 : ∀ c, φ (suroot σ hσσ 0 1 (by decide) (by decide) (by decide) c) = sb (tv 0 1 c))
    (hsb10 : ∀ c, φ (suroot σ hσσ 1 0 (by decide) (by decide) (by decide) c) = sb (tv 1 0 c)) :
    ∃ L : TwistedLayer H, L.lbZ = lbZ ∧ L.S = sb.range := by
  have hB2 : φ (suLetter σ hσ hσσ ι hι 2) * φ (suB σ hσ hσσ ι hι) =
      φ (suB σ hσ hσσ ι hι) * (φ (suLetter σ hσ hσσ ι hι 3) * φ (suLetter σ hσ hσσ ι hι 3)) := by
    have := congrArg φ (suLetter_conj2 σ hσ hσσ ι hι)
    simpa only [map_mul] using this
  have hB3 : φ (suLetter σ hσ hσσ ι hι 3) * φ (suB σ hσ hσσ ι hι) =
      φ (suB σ hσ hσσ ι hι) * (φ (suLetter σ hσ hσσ ι hι 2) * φ (suLetter σ hσ hσσ ι hι 2)) := by
    have := congrArg φ (suLetter_conj3 σ hσ hσσ ι hι)
    simpa only [map_mul] using this
  have hcube : ∀ j, φ (suLetter σ hσ hσσ ι hι j) * φ (suLetter σ hσ hσσ ι hι j) *
      φ (suLetter σ hσ hσσ ι hι j) = 1 := by
    intro j
    have := congrArg φ (suLetter_cube σ hσ hσσ ι hι j)
    simpa only [map_mul, map_one] using this
  have hinv : ∀ j, (φ (suLetter σ hσ hσσ ι hι j))⁻¹ =
      φ (suLetter σ hσ hσσ ι hι j) * φ (suLetter σ hσ hσσ ι hι j) :=
    fun j => inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hcube j)
  have hconj2 : (φ (suB σ hσ hσσ ι hι))⁻¹ * lbZ autXp * φ (suB σ hσ hσσ ι hι) =
      (lbZ autXm)⁻¹ := by
    rw [← hlbp, ← hlbm, hinv, mul_assoc, inv_mul_eq_iff_eq_mul]
    exact hB2
  have hconj3 : (φ (suB σ hσ hσσ ι hι))⁻¹ * lbZ autXm * φ (suB σ hσ hσσ ι hι) =
      (lbZ autXp)⁻¹ := by
    rw [← hlbp, ← hlbm, hinv, mul_assoc, inv_mul_eq_iff_eq_mul]
    exact hB3
  have hBlb : ∀ A, (φ (suB σ hσ hσσ ι hι))⁻¹ * lbZ A * φ (suB σ hσ hσσ ι hι) =
      lbZ ((absD 0)⁻¹ * A * absD 0) := by
    intro A
    have key : (MulAut.conj (φ (suB σ hσ hσσ ι hι))⁻¹).toMonoidHom.comp lbZ =
        lbZ.comp (MulAut.conj (absD 0)⁻¹).toMonoidHom := by
      refine hom_ext_of_gens ?_ ?_
      · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rw [absD0_inv_conj_xp, map_inv]
        exact hconj2
      · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rw [absD0_inv_conj_xm, map_inv]
        exact hconj3
    have := DFunLike.congr_fun key A
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      this
  have hBS : ∀ s ∈ sb.range,
      φ (suB σ hσ hσσ ι hι) * s * (φ (suB σ hσ hσσ ι hι))⁻¹ ∈ sb.range := by
    have h1 : ∀ x, ((MulAut.conj (φ (suB σ hσ hσσ ι hι))).toMonoidHom.comp sb) (tv 0 1 x) ∈
        sb.range := by
      intro x
      have h := congrArg φ (suB_conj01 σ hσ hσσ ι hι x)
      rw [map_mul, map_mul, map_inv, hsb01, hsb10] at h
      exact ⟨tv 1 0 (-σ x), by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
          h.symm⟩
    have h2 : ∀ x, ((MulAut.conj (φ (suB σ hσ hσσ ι hι))).toMonoidHom.comp sb) (tv 1 0 x) ∈
        sb.range := by
      intro x
      have h := congrArg φ (suB_conj10 σ hσ hσσ ι hι x)
      rw [map_mul, map_mul, map_inv, hsb01, hsb10] at h
      exact ⟨tv 0 1 (-σ x), by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
          h.symm⟩
    rintro _ ⟨A, rfl⟩
    exact sl2_mem_of_tv ((MulAut.conj (φ (suB σ hσ hσσ ι hι))).toMonoidHom.comp sb)
      (H := sb.range) h1 h2 A
  have hBS' : ∀ s ∈ sb.range,
      (φ (suB σ hσ hσσ ι hι))⁻¹ * s * φ (suB σ hσ hσσ ι hι) ∈ sb.range := by
    have h1 : ∀ x, ((MulAut.conj (φ (suB σ hσ hσσ ι hι))⁻¹).toMonoidHom.comp sb) (tv 0 1 x) ∈
        sb.range := by
      intro x
      have h := congrArg φ (suB_inv_conj01 σ hσ hσσ ι hι x)
      rw [map_mul, map_mul, map_inv, hsb01, hsb10] at h
      exact ⟨tv 1 0 (-σ x), by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          using h.symm⟩
    have h2 : ∀ x, ((MulAut.conj (φ (suB σ hσ hσσ ι hι))⁻¹).toMonoidHom.comp sb) (tv 1 0 x) ∈
        sb.range := by
      intro x
      have h := congrArg φ (suB_inv_conj10 σ hσ hσσ ι hι x)
      rw [map_mul, map_mul, map_inv, hsb01, hsb10] at h
      exact ⟨tv 0 1 (-σ x), by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          using h.symm⟩
    rintro _ ⟨A, rfl⟩
    have := sl2_mem_of_tv ((MulAut.conj (φ (suB σ hσ hσσ ι hι))⁻¹).toMonoidHom.comp sb)
      (H := sb.range) h1 h2 A
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      using this
  refine ⟨{ lbZ := lbZ, S := sb.range, e := fun j => φ (suLetter σ hσ hσσ ι hι j),
            rels := relsHold_hom φ (relsHold_suLetter σ hσ hσσ ι hι),
            e2 := hlbp, e3 := hlbm,
            eS6 := ⟨tv 0 1 1, (hsb01 1).symm⟩, eS7 := ⟨tv 0 1 ι, (hsb01 ι).symm⟩,
            eS8 := ⟨tv 1 0 1, (hsb10 1).symm⟩, eS9 := ⟨tv 1 0 ι, (hsb10 ι).symm⟩,
            B := φ (suB σ hσ hσσ ι hι), B_lb := hBlb, B_S := hBS, B_S' := hBS' }, rfl, rfl⟩

end Transport

section Layer

variable {E : Type} [Field E] [CharP E 3] (θ : E →+* E) (hθ : ∀ c, θ (θ c) = c)
  (hθ3 : ∀ x, θ x = x ^ 3) {ι : E} (hι : ι ^ 2 = -1) (e : ZMod 3 ≃+* fixedField θ)

include hθ3 hι in
theorem exists_twistedLayer_unitary :
    ∃ L : TwistedLayer (unitaryGroup θ hθ),
      L.lbZ = (ulb θ hθ).comp (Matrix.SpecialLinearGroup.map e.toRingHom) ∧
        L.S = (usb θ hθ).range :=
  exists_twistedLayer_of_hom (involEquiv θ hθ) hθ3 hθ ι hι
    (toU θ hθ hι (hθι_of θ hθ3 hι))
    ((ulb θ hθ).comp (Matrix.SpecialLinearGroup.map e.toRingHom)) (usb θ hθ)
    (toU_letter2 θ hθ hθ3 hι e) (toU_letter3 θ hθ hθ3 hι e)
    (toU_suroot01 θ hθ hθ3 hι) (toU_suroot10 θ hθ hθ3 hι)

end Layer

end CFSG.ClassicalInvolution.Q3.Q3E6T
