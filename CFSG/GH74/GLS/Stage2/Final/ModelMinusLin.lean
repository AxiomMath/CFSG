module

public import CFSG.GH74.GLS.Stage2.Final.ModelSpConj

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS.Stage2.Final.ModelSp

variable {F : Type} [Field F]

theorem bm_explicit (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    bm P Q R S = !![P 0 0, P 0 1, Q 0 0, Q 0 1; P 1 0, P 1 1, Q 1 0, Q 1 1; R 0 0, R 0 1, S 0 0, S 0 1;
      R 1 0, R 1 1, S 1 0, S 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bm, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
      e4_symm_zero, e4_symm_one, e4_symm_two, e4_symm_three, Matrix.fromBlocks]

@[expose] def ccmat (l m : F) : Matrix (Fin 4) (Fin 4) F :=
  !![l, 0, m, 0; 0, 1, 0, 0; -m, 0, l, 0; 0, 0, 0, 1]

theorem det_ccmat (l m : F) : (ccmat l m).det = l ^ 2 + m ^ 2 := by
  simp [ccmat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem wy_explicit : ((swapGL F * yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0] := by
  rw [coe_wy_bm, bm_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem ccmat_comm_wy (l m : F) :
    ccmat l m * ((swapGL F * yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((swapGL F * yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ccmat l m := by
  rw [wy_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ccmat, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] noncomputable def ccGL (l m : F) (h : l ^ 2 + m ^ 2 ≠ 0) : GL (Fin 4) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (ccmat l m) (by rw [det_ccmat]; exact h)

theorem coe_ccGL (l m : F) (h : l ^ 2 + m ^ 2 ≠ 0) :
    ((ccGL l m h : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = ccmat l m := rfl

theorem ccGL_comm_wy (l m : F) (h : l ^ 2 + m ^ 2 ≠ 0) :
    ccGL l m h * (swapGL F * yGL F) = (swapGL F * yGL F) * ccGL l m h := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_ccGL]
  exact ccmat_comm_wy l m

theorem nsm_conj_lin [Finite F] (h2 : (2 : F) ≠ 0) (a : GL (Fin 2) F) :
    ∃ k ∈ (ModelData.lin F).K4, k * (swapGL F * yGL F) * k⁻¹ = swapGL F * diagGL a (-a⁻¹) := by
  have hδ : ((Matrix.GeneralLinearGroup.det (-a) : Fˣ) : F) ≠ 0 := Units.ne_zero _
  obtain ⟨l, m, hlm⟩ := exists_sq_add_sq h2 (((Matrix.GeneralLinearGroup.det (-a) : Fˣ) : F)⁻¹)
  have hne : l ^ 2 + m ^ 2 ≠ 0 := by rw [hlm]; exact inv_ne_zero hδ
  refine ⟨diagGL 1 (-a) * ccGL l m hne, ((ModelData.lin F).mem_K4 _).2 ⟨Subgroup.mem_top _, ?_⟩, ?_⟩
  · rw [Units.val_mul, Matrix.det_mul, det_diagGL, coe_ccGL, det_ccmat, hlm]
    have := Matrix.GeneralLinearGroup.val_det_apply (-a)
    rw [Units.val_one, Matrix.det_one, one_mul, ← this]
    exact mul_inv_cancel₀ hδ
  · have hc := ccGL_comm_wy l m hne
    calc diagGL 1 (-a) * ccGL l m hne * (swapGL F * yGL F) * (diagGL 1 (-a) * ccGL l m hne)⁻¹
        = diagGL 1 (-a) * (ccGL l m hne * (swapGL F * yGL F) * (ccGL l m hne)⁻¹) *
            (diagGL 1 (-a))⁻¹ := by group
      _ = diagGL 1 (-a) * (swapGL F * yGL F) * (diagGL 1 (-a))⁻¹ := by
          rw [hc, mul_assoc (swapGL F * yGL F), mul_inv_cancel, mul_one]
      _ = swapGL F * diagGL (-(-a)) (-a)⁻¹ := nsm_core (-a)
      _ = swapGL F * diagGL a (-a⁻¹) := by rw [neg_neg, inv_neg]

theorem JJ_explicit : ((diagGL (J0 F) (J0 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  rw [coe_diagGL, blk4_eq_bm, bm_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_J0]

@[expose] def jjk (l m : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 0, l, m; 0, 1, 0, 0; 0, 0, -m, l]

theorem det_jjk (l m : F) : (jjk l m).det = -(l ^ 2 + m ^ 2) := by
  simp [jjk, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem jjk_intertwine (l m : F) :
    jjk l m * ((diagGL (J0 F) (J0 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((swapGL F * yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * jjk l m := by
  rw [JJ_explicit, wy_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jjk, Matrix.mul_apply, Fin.sum_univ_four]

theorem jj_conj_lin [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ k ∈ (ModelData.lin F).K4, k * diagGL (J0 F) (J0 F) * k⁻¹ = swapGL F * yGL F := by
  obtain ⟨l, m, hlm⟩ := exists_sq_add_sq h2 (-1)
  have hdet : (jjk l m).det = 1 := by rw [det_jjk, hlm]; ring
  let k : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (jjk l m) (by rw [hdet]; exact one_ne_zero)
  refine ⟨k, ((ModelData.lin F).mem_K4 _).2 ⟨Subgroup.mem_top _, hdet⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact jjk_intertwine l m

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
