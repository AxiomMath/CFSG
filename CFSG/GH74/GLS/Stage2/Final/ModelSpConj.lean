module

public import CFSG.GH74.GLS.Stage2.Final.ModelMinus
public import CFSG.GH74.GLS.Stage2.Final.ModelLUElts

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS.Stage2.Final.ModelSp

variable {F : Type} [Field F]

@[expose] def bm (P Q R S : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.reindexAlgEquiv F F e4 (Matrix.fromBlocks P Q R S)

theorem bm_mul (P Q R S P' Q' R' S' : Matrix (Fin 2) (Fin 2) F) :
    bm P Q R S * bm P' Q' R' S' =
      bm (P * P' + Q * R') (P * Q' + Q * S') (R * P' + S * R') (R * Q' + S * S') := by
  rw [bm, bm, bm, ← map_mul, Matrix.fromBlocks_multiply]

theorem bm_add (P Q R S P' Q' R' S' : Matrix (Fin 2) (Fin 2) F) :
    bm P Q R S + bm P' Q' R' S' = bm (P + P') (Q + Q') (R + R') (S + S') := by
  rw [bm, bm, bm, ← map_add, Matrix.fromBlocks_add]

theorem bm_transpose (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    (bm P Q R S)ᵀ = bm Pᵀ Rᵀ Qᵀ Sᵀ := by
  simp only [bm, Matrix.coe_reindexAlgEquiv]
  rw [Matrix.transpose_reindex, Matrix.fromBlocks_transpose]

theorem bm_inj {P Q R S P' Q' R' S' : Matrix (Fin 2) (Fin 2) F}
    (h : bm P Q R S = bm P' Q' R' S') : P = P' ∧ Q = Q' ∧ R = R' ∧ S = S' := by
  have h' := (Matrix.reindexAlgEquiv F F e4).injective h
  exact Matrix.fromBlocks_inj.1 h'

theorem bm_one : (1 : Matrix (Fin 4) (Fin 4) F) = bm 1 0 0 1 := by
  rw [bm, Matrix.fromBlocks_one, map_one]

theorem blk4_eq_bm (X Y : Matrix (Fin 2) (Fin 2) F) : blk4 X Y = bm X 0 0 Y :=
  blk4_eq_reindex X Y

theorem wMat_eq_bm : (wMat : Matrix (Fin 4) (Fin 4) F) = bm 0 1 1 0 := rfl

theorem bm_neg (P Q R S : Matrix (Fin 2) (Fin 2) F) : -bm P Q R S = bm (-P) (-Q) (-R) (-S) := by
  rw [bm, bm, ← map_neg, Matrix.fromBlocks_neg]

theorem bm_smul (c : F) (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    c • bm P Q R S = bm (c • P) (c • Q) (c • R) (c • S) := by
  rw [bm, bm, ← map_smul, Matrix.fromBlocks_smul]

theorem kw_symp (a : Matrix (Fin 2) (Fin 2) F) (hT : aᵀ * J2m F * a = (2⁻¹ : F) • J2m F) (h2 : (2 : F) ≠ 0) :
    (bm a a (-a) a)ᵀ * blk4 (J2m F) (J2m F) * bm a a (-a) a = blk4 (J2m F) (J2m F) := by
  rw [bm_transpose, blk4_eq_bm, bm_mul, bm_mul]
  simp only [Matrix.transpose_neg, mul_zero, zero_add, add_zero, mul_neg, neg_mul, neg_neg]
  rw [hT, add_neg_cancel, ← add_smul]
  have h : ((2 : F)⁻¹ + 2⁻¹) = 1 := by field_simp; norm_num
  rw [h, one_smul]

theorem coe_xyGL_bm : ((xyGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = bm 1 0 0 (-1) := by
  rw [xyGL, coe_diagGL, blk4_eq_bm, Units.val_one, Units.val_neg, Units.val_one]

theorem coe_yGL_bm : ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = bm (-1) 0 0 1 := by
  rw [yGL, coe_diagGL, blk4_eq_bm, Units.val_one, Units.val_neg, Units.val_one]

theorem det_Omega : (blk4 (J2m F) (J2m F)).det = 1 := by
  rw [det_blk4]; simp [J2m, Matrix.det_fin_two]

theorem exists_sp_of_symp (k : Matrix (Fin 4) (Fin 4) F)
    (hk : kᵀ * blk4 (J2m F) (J2m F) * k = blk4 (J2m F) (J2m F)) :
    ∃ g : GL (Fin 4) F, (g : Matrix (Fin 4) (Fin 4) F) = k ∧ g ∈ (ModelData.sp F).K4 := by
  have hdet : k.det ≠ 0 := by
    have := congrArg Matrix.det hk
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_Omega] at this
    intro h
    rw [h] at this
    simp at this
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero k hdet, rfl, ?_⟩
  rw [K4_sp_eq, mem_isoGL]
  exact hk

theorem w_conj_sp (h2 : (2 : F) ≠ 0) :
    ∃ k ∈ (ModelData.sp F).K4, k * swapGL F * k⁻¹ = xyGL F := by
  set a : Matrix (Fin 2) (Fin 2) F := !![2⁻¹, 0; 0, 1] with ha
  have hdet : a.det = 2⁻¹ := by simp [a, Matrix.det_fin_two]
  have hT : aᵀ * J2m F * a = (2⁻¹ : F) • J2m F := by rw [transpose_mul_J2m_mul, hdet]
  obtain ⟨g, hg, hgK⟩ := exists_sp_of_symp (bm a a (-a) a) (kw_symp a hT h2)
  refine ⟨g, hgK, ?_⟩
  have h : g * swapGL F = xyGL F * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hg, coe_swapGL, wMat_eq_bm, coe_xyGL_bm, bm_mul, bm_mul]
    simp only [mul_zero, mul_one, zero_add, add_zero, neg_mul, zero_mul, one_mul, mul_neg, neg_neg,
      neg_zero]
  rw [mul_inv_eq_iff_eq_mul]
  exact h

theorem coe_wy_bm : (((swapGL F * yGL F : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
    bm 0 1 (-1) 0 := by
  rw [Units.val_mul, coe_swapGL, wMat_eq_bm, coe_yGL_bm, bm_mul]
  simp

theorem nsm_core (b : GL (Fin 2) F) :
    diagGL 1 b * (swapGL F * yGL F) * (diagGL 1 b)⁻¹ = swapGL F * diagGL (-b) b⁻¹ := by
  have h1 : diagGL 1 b * swapGL F * (diagGL 1 b)⁻¹ = swapGL F * diagGL b b⁻¹ := diag_swap_conj b
  have h2 : diagGL 1 b * yGL F * (diagGL 1 b)⁻¹ = yGL F := by
    rw [mul_inv_eq_iff_eq_mul]
    exact diagGL_comm_yGL (F := F) 1 b
  calc diagGL 1 b * (swapGL F * yGL F) * (diagGL 1 b)⁻¹
      = (diagGL 1 b * swapGL F * (diagGL 1 b)⁻¹) * (diagGL 1 b * yGL F * (diagGL 1 b)⁻¹) := by group
    _ = swapGL F * diagGL b b⁻¹ * yGL F := by rw [h1, h2]
    _ = swapGL F * diagGL (-b) b⁻¹ := by
        rw [mul_assoc, yGL, diagGL_mul]
        simp

theorem ns_conj_sp (a : GL (Fin 2) F) (ha : a ∈ (ModelData.sp F).U2) :
    ∃ k ∈ (ModelData.sp F).K4, k * swapGL F * k⁻¹ = swapGL F * diagGL a a⁻¹ := by
  refine ⟨diagGL 1 a, (ModelData.sp F).diagGL_mem_K4_iff.2 ⟨(ModelData.sp F).U2.one_mem, ha, ?_⟩,
    diag_swap_conj a⟩
  rw [mem_U2_sp.1 ha]
  simp

theorem nsm_conj_sp (a : GL (Fin 2) F) (ha : a ∈ (ModelData.sp F).U2) :
    ∃ k ∈ (ModelData.sp F).K4, k * (swapGL F * yGL F) * k⁻¹ = swapGL F * diagGL a (-a⁻¹) := by
  have hna : -a ∈ (ModelData.sp F).U2 := by
    have := (ModelData.sp F).U2.mul_mem (ModelData.sp F).neg_mem ha
    simpa using this
  refine ⟨diagGL 1 (-a), (ModelData.sp F).diagGL_mem_K4_iff.2 ⟨(ModelData.sp F).U2.one_mem, hna, ?_⟩, ?_⟩
  · rw [mem_U2_sp.1 hna]
    simp
  · rw [nsm_core, neg_neg, inv_neg]

@[expose] def jjP (F : Type) [Field F] : Matrix (Fin 2) (Fin 2) F := !![0, -(2⁻¹ : F); 1, 0]
@[expose] def jjQ (g0 g1 : F) : Matrix (Fin 2) (Fin 2) F := !![g0, g1 / 2; g1, -2 * g0]
@[expose] def jjR (F : Type) [Field F] : Matrix (Fin 2) (Fin 2) F := !![2⁻¹, 0; 0, 1]
@[expose] def jjS (g0 g1 : F) : Matrix (Fin 2) (Fin 2) F := !![-(g1 / 2), g0; 2 * g0, g1]

theorem jj_intertwine (g0 g1 : F) :
    bm (jjP F) (jjQ g0 g1) (jjR F) (jjS g0 g1) * bm (J0 F : Matrix (Fin 2) (Fin 2) F) 0 0 (J0 F) =
      bm 0 1 (-1) 0 * bm (jjP F) (jjQ g0 g1) (jjR F) (jjS g0 g1) := by
  rw [bm_mul, bm_mul]
  simp only [mul_zero, add_zero, zero_mul, zero_add, one_mul, neg_mul]
  have e1 : jjP F * (J0 F : Matrix (Fin 2) (Fin 2) F) = jjR F := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jjP, jjR, coe_J0, Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : jjQ g0 g1 * (J0 F : Matrix (Fin 2) (Fin 2) F) = jjS g0 g1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jjQ, jjS, coe_J0, Matrix.mul_apply, Fin.sum_univ_two]
  have e3 : jjR F * (J0 F : Matrix (Fin 2) (Fin 2) F) = -jjP F := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jjP, jjR, coe_J0, Matrix.mul_apply, Fin.sum_univ_two]
  have e4 : jjS g0 g1 * (J0 F : Matrix (Fin 2) (Fin 2) F) = -jjQ g0 g1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jjQ, jjS, coe_J0, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e1, e2, e3, e4]

theorem jj_symp (g0 g1 : F) (h2 : (2 : F) ≠ 0) (hg : g1 ^ 2 + 4 * g0 ^ 2 = -1) :
    (bm (jjP F) (jjQ g0 g1) (jjR F) (jjS g0 g1))ᵀ * blk4 (J2m F) (J2m F) *
      bm (jjP F) (jjQ g0 g1) (jjR F) (jjS g0 g1) = blk4 (J2m F) (J2m F) := by
  rw [bm_transpose, blk4_eq_bm, bm_mul, bm_mul]
  simp only [mul_zero, zero_add, add_zero]
  have e1 : (jjP F)ᵀ * J2m F * jjP F + (jjR F)ᵀ * J2m F * jjR F = J2m F := by
    rw [transpose_mul_J2m_mul, transpose_mul_J2m_mul, ← add_smul]
    have h1 : (jjP F).det = 2⁻¹ := by simp [jjP, Matrix.det_fin_two]
    have h2' : (jjR F).det = 2⁻¹ := by simp [jjR, Matrix.det_fin_two]
    rw [h1, h2']
    have h : ((2 : F)⁻¹ + 2⁻¹) = 1 := by field_simp; norm_num
    rw [h, one_smul]
  have e4 : (jjQ g0 g1)ᵀ * J2m F * jjQ g0 g1 + (jjS g0 g1)ᵀ * J2m F * jjS g0 g1 = J2m F := by
    rw [transpose_mul_J2m_mul, transpose_mul_J2m_mul, ← add_smul]
    have h1 : (jjQ g0 g1).det = -2 * g0 ^ 2 - g1 ^ 2 / 2 := by
      simp [jjQ, Matrix.det_fin_two]; ring
    have h2' : (jjS g0 g1).det = -(g1 ^ 2) / 2 - 2 * g0 ^ 2 := by
      simp [jjS, Matrix.det_fin_two]; ring
    rw [h1, h2']
    have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    have h : (-2 * g0 ^ 2 - g1 ^ 2 / 2 + (-(g1 ^ 2) / 2 - 2 * g0 ^ 2)) = 1 := by
      linear_combination -hg - g1 ^ 2 * h22
    rw [h, one_smul]
  have e2 : (jjP F)ᵀ * J2m F * jjQ g0 g1 + (jjR F)ᵀ * J2m F * jjS g0 g1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jjP, jjQ, jjR, jjS, J2m, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
      field_simp <;> ring
  have e3 : (jjQ g0 g1)ᵀ * J2m F * jjP F + (jjS g0 g1)ᵀ * J2m F * jjR F = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jjP, jjQ, jjR, jjS, J2m, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
      field_simp <;> ring
  rw [e1, e2, e3, e4]

theorem jj_conj_sp [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ k ∈ (ModelData.sp F).K4, k * diagGL (J0 F) (J0 F) * k⁻¹ = swapGL F * yGL F := by
  obtain ⟨l, m, hlm⟩ := exists_sq_add_sq h2 (-1)
  have hg : l ^ 2 + 4 * (m / 2) ^ 2 = -1 := by
    rw [← hlm]
    field_simp
    ring
  obtain ⟨g, hg', hgK⟩ := exists_sp_of_symp _ (jj_symp (m / 2) l h2 hg)
  refine ⟨g, hgK, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg', coe_diagGL, blk4_eq_bm, coe_wy_bm]
  exact jj_intertwine (m / 2) l

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
