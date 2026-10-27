module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

variable {F : Type} [Field F]

@[expose] def cSL : SpecialLinearGroup (Fin 2) F := ⟨cMat, cMat_det⟩

theorem toGL_cSL : (Matrix.SpecialLinearGroup.toGL (cSL (F := F))) = cGL := Units.ext rfl

theorem orderOf_cSL : orderOf (cSL (F := F)) = 3 := by
  rw [← orderOf_injective _ (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := F)) cSL,
    toGL_cSL, orderOf_cGL]

theorem eq_one_of_mem_center_of_pow_three {z : SpecialLinearGroup (Fin 2) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) (h : z ^ 3 = 1) : z = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  have hzm : (z : Matrix (Fin 2) (Fin 2) F) = r • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hrz]
    simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have h3 : (z : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  rw [hzm, smul_pow, one_pow] at h3
  have hr3 : r ^ 3 = 1 := by
    have := congrFun (congrFun h3 0) 0
    simpa using this
  have hr1 : r = 1 := by
    calc r = r * r ^ 2 := by rw [hr, mul_one]
      _ = r ^ 3 := by ring
      _ = 1 := hr3
  refine Subtype.ext ?_
  rw [hzm, hr1, one_smul]
  rfl

variable [Fintype F]

theorem exists_comm_det_eq (h3 : (3 : F) ≠ 0) {d : F} (hd : d ≠ 0) :
    ∃ n : GL (Fin 2) F, (n : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (n : Matrix (Fin 2) (Fin 2) F) ∧
      (n : Matrix (Fin 2) (Fin 2) F).det = d := by
  obtain ⟨s, hs, hdet⟩ := exists_pairMat_det_eq h3 hd
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (pairMat cMat s) (by rw [hdet]; exact hd), ?_, hdet⟩
  exact pairMat_mul_cMat cMat_relation s

omit [Fintype F] in
theorem swap_conj_cGL : (GeneralLinearGroup.mkOfDetNeZero (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)
      (by simp [Matrix.det_fin_two])) * cGL *
    (GeneralLinearGroup.mkOfDetNeZero (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)
      (by simp [Matrix.det_fin_two]))⁻¹ = cGL⁻¹ := by
  set sw : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)
    (by simp [Matrix.det_fin_two]) with hsw
  have hswsw : sw * sw = 1 := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hsw, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply,
      Fin.sum_univ_two]
  have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hswsw
  rw [hswinv, eq_inv_iff_mul_eq_one]
  refine Units.ext ?_
  simp only [Units.val_mul, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hsw, GeneralLinearGroup.mkOfDetNeZero, coe_cGL, cMat, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem exists_inverting_det_one (h3 : (3 : F) ≠ 0) :
    ∃ s : GL (Fin 2) F, (s : Matrix (Fin 2) (Fin 2) F).det = 1 ∧ s * cGL * s⁻¹ = cGL⁻¹ := by
  have hm1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  obtain ⟨n, hn, hdn⟩ := exists_comm_det_eq h3 hm1
  set sw : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) (by simp [Matrix.det_fin_two]) with hsw
  have hnc : n * cGL = cGL * n := Units.ext hn
  refine ⟨sw * n⁻¹, ?_, ?_⟩
  · have hsdet : (sw : Matrix (Fin 2) (Fin 2) F).det = -1 := by
      simp [hsw, GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]
    have hinv : ((n⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
        ((n : Matrix (Fin 2) (Fin 2) F).det)⁻¹ := by
      rw [← GeneralLinearGroup.val_det_apply, ← GeneralLinearGroup.val_det_apply, map_inv,
        Units.val_inv_eq_inv_val]
    rw [Units.val_mul, Matrix.det_mul, hinv, hsdet, hdn]
    exact mul_inv_cancel₀ hm1
  · have hconj : n⁻¹ * cGL * n = cGL := by
      rw [mul_assoc, ← hnc, inv_mul_cancel_left]
    calc sw * n⁻¹ * cGL * (sw * n⁻¹)⁻¹ = sw * (n⁻¹ * cGL * n) * sw⁻¹ := by group
      _ = sw * cGL * sw⁻¹ := by rw [hconj]
      _ = cGL⁻¹ := swap_conj_cGL

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
