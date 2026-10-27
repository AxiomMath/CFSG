module

public import CFSG.ClassicalGroups.Symplectic.WedgeTwo
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef
import CFSG.RankThree.PartOne.KC.SymplecticSemi
import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd

public section

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

open Matrix CFSG.Open CFSG.ClassicalGroups.Symplectic.WedgeTwo
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

instance instFactPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem quadGram5_zmod_five : quadGram5 (ZMod 5) = soGram5 := rfl

abbrev gspMatrix (A : gsp 2 (ZMod 5)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  ((A : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5))

@[expose] noncomputable def gspMultiplier (A : gsp 2 (ZMod 5)) : ZMod 5 :=
  (multiplier 2 (ZMod 5) A : ZMod 5)

theorem gspMatrix_spec (A : gsp 2 (ZMod 5)) :
    (gspMatrix A)ᵀ * wedgeJ (ZMod 5) * gspMatrix A = gspMultiplier A • wedgeJ (ZMod 5) :=
  multiplier_spec A

theorem gspMultiplier_ne_zero (A : gsp 2 (ZMod 5)) : gspMultiplier A ≠ 0 :=
  (multiplier 2 (ZMod 5) A).ne_zero

theorem gspMultiplier_mul (A B : gsp 2 (ZMod 5)) :
    gspMultiplier (A * B) = gspMultiplier A * gspMultiplier B := by
  simp [gspMultiplier, map_mul]

theorem gspMultiplier_one : gspMultiplier (1 : gsp 2 (ZMod 5)) = 1 := by
  simp [gspMultiplier]

@[expose] noncomputable def wedgePre (A : gsp 2 (ZMod 5)) : SoMat5 :=
  (gspMultiplier A)⁻¹ • wedgeRestrict (gspMatrix A)

theorem wedgePre_gram (A : gsp 2 (ZMod 5)) :
    (wedgePre A)ᵀ * soGram5 * wedgePre A = soGram5 := by
  have h := wedgeRestrict_gram (gspMatrix_spec A)
  rw [quadGram5_zmod_five] at h
  simp only [wedgePre, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul]
  rw [show (gspMultiplier A)⁻¹ * ((gspMultiplier A)⁻¹ * gspMultiplier A ^ 2) = 1 by
    field_simp [gspMultiplier_ne_zero A], one_smul]

theorem wedgePre_mul (A B : gsp 2 (ZMod 5)) : wedgePre (A * B) = wedgePre A * wedgePre B := by
  have h : gspMatrix (A * B) = gspMatrix A * gspMatrix B := rfl
  simp only [wedgePre, gspMultiplier_mul, h, wedgeRestrict_mul _ (gspMatrix_spec B),
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv]
  rw [mul_comm (gspMultiplier A)⁻¹]

theorem wedgePre_one : wedgePre (1 : gsp 2 (ZMod 5)) = 1 := by
  have h : gspMatrix (1 : gsp 2 (ZMod 5)) = 1 := rfl
  simp [wedgePre, gspMultiplier_one, h, wedgeRestrict_one]

theorem det_soGram5 : soGram5.det = 2 := by
  simp [soGram5, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem wedgePre_det_sq (A : gsp 2 (ZMod 5)) : (wedgePre A).det ^ 2 = 1 := by
  have h := congrArg Matrix.det (wedgePre_gram A)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_soGram5] at h
  have h3 : (2 : ZMod 5) ≠ 0 := by decide
  have : ((wedgePre A).det ^ 2 - 1) * 2 = 0 := by linear_combination h
  simpa [sub_eq_zero, h3] using this

@[expose] noncomputable def wedgeFin (A : gsp 2 (ZMod 5)) : SoMat5 :=
  (wedgePre A).det • wedgePre A

theorem wedgeFin_det (A : gsp 2 (ZMod 5)) : (wedgeFin A).det = 1 := by
  rw [wedgeFin, Matrix.det_smul, Fintype.card_fin]
  have h := wedgePre_det_sq A
  calc (wedgePre A).det ^ 5 * (wedgePre A).det = ((wedgePre A).det ^ 2) ^ 3 := by ring
    _ = 1 := by rw [h, one_pow]

theorem wedgeFin_gram (A : gsp 2 (ZMod 5)) : (wedgeFin A)ᵀ * soGram5 * wedgeFin A = soGram5 := by
  simp only [wedgeFin, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, wedgePre_gram,
    smul_smul]
  rw [← pow_two, wedgePre_det_sq, one_smul]

theorem wedgeFin_mul (A B : gsp 2 (ZMod 5)) : wedgeFin (A * B) = wedgeFin A * wedgeFin B := by
  simp only [wedgeFin, wedgePre_mul, Matrix.det_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (wedgePre B).det]

theorem wedgeFin_one : wedgeFin (1 : gsp 2 (ZMod 5)) = 1 := by
  simp [wedgeFin, wedgePre_one]

@[expose] noncomputable def gspToSoGroup5 : gsp 2 (ZMod 5) →* soGroup5 where
  toFun A := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (wedgeFin A)
    (by rw [wedgeFin_det]; exact one_ne_zero), wedgeFin_gram A, wedgeFin_det A⟩
  map_one' := by ext : 2; simp [wedgeFin_one]
  map_mul' A B := by ext : 2; simp [wedgeFin_mul]

theorem gspToSoGroup5_apply (A : gsp 2 (ZMod 5)) :
    ((gspToSoGroup5 A : GL (Fin 5) (ZMod 5)) : SoMat5) = wedgeFin A := rfl

theorem gspToSoGroup5_scalar (A : gsp 2 (ZMod 5)) (c : (ZMod 5)ˣ)
    (hA : (A : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c) : gspToSoGroup5 A = 1 := by
  have hm : gspMatrix A = (c : ZMod 5) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) := by
    rw [show gspMatrix A = ((A : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) : Matrix _ _ _) from rfl, hA]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, hij]
  have hmu : gspMultiplier A = (c : ZMod 5) ^ 2 := by
    have h := gspMatrix_spec A
    rw [hm] at h
    have h2 := congrFun (congrFun h (.inl 0)) (.inr 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply] at h2
    linear_combination -h2
  have hc : (c : ZMod 5) ≠ 0 := c.ne_zero
  have hpre : wedgePre A = 1 := by
    rw [wedgePre, hm, wedgeRestrict_smul, wedgeRestrict_one, hmu, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hc), one_smul]
  ext : 2
  simp [gspToSoGroup5_apply, wedgeFin, hpre]

theorem ker_conjAut_le_ker : (conjAut 2 (ZMod 5)).ker ≤ gspToSoGroup5.ker := by
  intro A hA
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCSpComm.conjAut_eq_one_iff (by norm_num) A).mp hA
  exact gspToSoGroup5_scalar A c hc

@[expose] noncomputable def rangeToSoGroup5 : (conjAut 2 (ZMod 5)).range →* soGroup5 :=
  (QuotientGroup.lift _ gspToSoGroup5 ker_conjAut_le_ker).comp
    (QuotientGroup.quotientKerEquivRange (conjAut 2 (ZMod 5))).symm.toMonoidHom

theorem rangeToSoGroup5_apply (A : gsp 2 (ZMod 5)) :
    rangeToSoGroup5 ⟨conjAut 2 (ZMod 5) A, A, rfl⟩ = gspToSoGroup5 A := by
  have : (QuotientGroup.quotientKerEquivRange (conjAut 2 (ZMod 5))).symm
      ⟨conjAut 2 (ZMod 5) A, A, rfl⟩ =
      (QuotientGroup.mk A : gsp 2 (ZMod 5) ⧸ (conjAut 2 (ZMod 5)).ker) := by
    rw [MulEquiv.symm_apply_eq]; rfl
  simp only [rangeToSoGroup5, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this,
    QuotientGroup.lift_mk]

theorem range_conjAut_eq_top : (conjAut 2 (ZMod 5)).range = ⊤ := by
  refine eq_top_iff.mpr fun α _ => ?_
  obtain ⟨A, σ, hα⟩ := CFSG.RankThree.PartTwo.KFacts.psp4_odd_automorphism_normal_form
    (K := ZMod 5) (by rw [ZMod.ringChar_zmod_n]; decide) α
  have hσ : σ = 1 := Subsingleton.elim _ _
  exact ⟨A, by rw [hα, hσ, map_one, mul_one]⟩

@[expose] def diagTwoOneThreeOne : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  Matrix.diagonal (Sum.elim ![2, 1] ![3, 1])

theorem diagTwoOneThreeOne_symplectic :
    (diagTwoOneThreeOne)ᵀ * wedgeJ (ZMod 5) * diagTwoOneThreeOne = wedgeJ (ZMod 5) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [diagTwoOneThreeOne, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.diagonal_apply] <;> decide

theorem diagTwoOneThreeOne_det_ne_zero : diagTwoOneThreeOne.det ≠ 0 := by
  simp [diagTwoOneThreeOne, Matrix.det_diagonal, Fintype.prod_sum_type, Fin.prod_univ_two]
  decide

@[expose] noncomputable def diagTwoOneThreeOneGsp : gsp 2 (ZMod 5) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero diagTwoOneThreeOne diagTwoOneThreeOne_det_ne_zero,
    ⟨1, by simpa using diagTwoOneThreeOne_symplectic⟩⟩

theorem gspToSoGroup5_diag_ne_one : gspToSoGroup5 diagTwoOneThreeOneGsp ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : soGroup5 => ((g : GL (Fin 5) (ZMod 5)) : SoMat5) 0 0) h
  have hmu : gspMultiplier diagTwoOneThreeOneGsp = 1 := by
    unfold gspMultiplier
    rw [multiplier_eq diagTwoOneThreeOneGsp (μ := 1)
      (by simpa [diagTwoOneThreeOneGsp] using diagTwoOneThreeOne_symplectic)]
    rfl
  have hd := wedgePre_det_sq diagTwoOneThreeOneGsp
  simp only [gspToSoGroup5_apply, OneMemClass.coe_one, Units.val_one, Matrix.one_apply_eq] at h1
  have h00 : wedgePre diagTwoOneThreeOneGsp 0 0 = 2 := by
    have hg : gspMatrix diagTwoOneThreeOneGsp = diagTwoOneThreeOne := rfl
    rw [wedgePre, hmu, inv_one, one_smul, hg, wedgeRestrict_apply_zero_zero,
      wedge2_apply_zero_zero]
    simp [diagTwoOneThreeOne, Matrix.diagonal_apply]
  have h3 : (wedgePre diagTwoOneThreeOneGsp).det * 2 = 1 := by
    have : (wedgeFin diagTwoOneThreeOneGsp) 0 0 =
        (wedgePre diagTwoOneThreeOneGsp).det * wedgePre diagTwoOneThreeOneGsp 0 0 := by
      simp [wedgeFin]
    rw [← h00, ← this]; exact h1
  have h4 : ((wedgePre diagTwoOneThreeOneGsp).det - 1) *
      ((wedgePre diagTwoOneThreeOneGsp).det + 1) = 0 := by linear_combination hd
  rcases mul_eq_zero.mp h4 with h5 | h5
  · rw [sub_eq_zero.mp h5] at h3; revert h3; decide
  · rw [eq_neg_of_add_eq_zero_left h5] at h3; revert h3; decide

end CFSG.EvenSporadicStandard.TwoHS.GH312
