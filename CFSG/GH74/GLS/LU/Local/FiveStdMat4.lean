module

public import CFSG.GH74.GLS.LU.Local.FiveStdMat3
public import CFSG.GH74.GLS.LU.Local.FiveStdDict
public import CFSG.GH74.L5U5.ModelsPairs

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd.Mat

open CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock Matrix

variable {F : Type} [Field F] [CharP F 5]

theorem mat4_row0_false (x : E) (h : x.s = false) :
    (mat4 x : Matrix (Fin 4) (Fin 4) F) 0 0 = cF F x.a0 ∧ (mat4 x : Matrix (Fin 4) (Fin 4) F) 0 1 = cF F x.a1 ∧
      (mat4 x : Matrix (Fin 4) (Fin 4) F) 0 2 = 0 ∧ (mat4 x : Matrix (Fin 4) (Fin 4) F) 0 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [mat4, h, blk4_apply, blkA, mkM, e4_symm_zero, e4_symm_one, e4_symm_two, e4_symm_three]

theorem mat4_row0_true (x : E) (h : x.s = true) :
    (mat4 x : Matrix (Fin 4) (Fin 4) F) 0 0 = 0 ∧ (mat4 x : Matrix (Fin 4) (Fin 4) F) 0 1 = 0 ∧
      (mat4 x : Matrix (Fin 4) (Fin 4) F) 0 2 = cF F x.a0 ∧ (mat4 x : Matrix (Fin 4) (Fin 4) F) 0 3 = cF F x.a1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [mat4, h, blk4_apply, wMat, Matrix.mul_apply, Fin.sum_univ_four, blkA, mkM, e4_symm_zero, e4_symm_one,
      e4_symm_two, e4_symm_three]

theorem isNorm_iff (x : E) : isNorm x = true ↔ x.a0 = 1 ∨ (x.a0 = 0 ∧ x.a1 = 1) := by
  simp [isNorm]

theorem blocks_of_mat4_smul {x y : E} (hs : y.s = x.s) (c : F)
    (h : (mat4 y : Matrix (Fin 4) (Fin 4) F) = c • mat4 x) :
    (blkA y : Matrix (Fin 2) (Fin 2) F) = c • blkA x ∧ (blkB y : Matrix (Fin 2) (Fin 2) F) = c • blkB x := by
  have h' : blk4 (blkA y : Matrix (Fin 2) (Fin 2) F) (blkB y) = c • blk4 (blkA x : Matrix (Fin 2) (Fin 2) F) (blkB x) := by
    cases hxs : x.s
    · have hys : y.s = false := hs.trans hxs
      simpa [mat4, hxs, hys] using h
    · have hys : y.s = true := hs.trans hxs
      have h2 := congrArg (fun M => M * (wMat : Matrix (Fin 4) (Fin 4) F)) h
      simpa [mat4, hxs, hys, Matrix.mul_assoc, wMat_mul_self, Matrix.smul_mul] using h2
  rw [← blk4_smul] at h'
  exact blk4_inj h'

theorem eq_of_mat4_smul {x y : E} (hx : validE x = true) (hy : validE y = true) (c : F)
    (h : (mat4 y : Matrix (Fin 4) (Fin 4) F) = c • mat4 x) : x = y := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h1 := det_mat4_valid (F := F) hy
    rw [h, zero_smul, Matrix.det_zero] at h1
    exact zero_ne_one h1
  have hxA := (det_ne_zero_of_valid hx).1
  have hs : y.s = x.s := by
    cases hxs : x.s <;> cases hys : y.s
    · rfl
    · exfalso
      have e0 := congrFun (congrFun h 0) 0
      have e1 := congrFun (congrFun h 0) 1
      obtain ⟨hy00, hy01, -, -⟩ := mat4_row0_true (F := F) y hys
      obtain ⟨hx00, hx01, -, -⟩ := mat4_row0_false (F := F) x hxs
      simp only [Matrix.smul_apply, smul_eq_mul, hy00, hx00] at e0
      simp only [Matrix.smul_apply, smul_eq_mul, hy01, hx01] at e1
      have ha0 : x.a0 = 0 := cF_eq_zero.1 ((mul_eq_zero.1 e0.symm).resolve_left hc)
      have ha1 : x.a1 = 0 := cF_eq_zero.1 ((mul_eq_zero.1 e1.symm).resolve_left hc)
      exact hxA (by simp [detA, ha0, ha1])
    · exfalso
      have e0 := congrFun (congrFun h 0) 2
      have e1 := congrFun (congrFun h 0) 3
      obtain ⟨-, -, hy02, hy03⟩ := mat4_row0_false (F := F) y hys
      obtain ⟨-, -, hx02, hx03⟩ := mat4_row0_true (F := F) x hxs
      simp only [Matrix.smul_apply, smul_eq_mul, hy02, hx02] at e0
      simp only [Matrix.smul_apply, smul_eq_mul, hy03, hx03] at e1
      have ha0 : x.a0 = 0 := cF_eq_zero.1 ((mul_eq_zero.1 e0.symm).resolve_left hc)
      have ha1 : x.a1 = 0 := cF_eq_zero.1 ((mul_eq_zero.1 e1.symm).resolve_left hc)
      exact hxA (by simp [detA, ha0, ha1])
    · rfl
  obtain ⟨hA, hB⟩ := blocks_of_mat4_smul hs c h
  have a0 := congrFun (congrFun hA 0) 0
  have a1 := congrFun (congrFun hA 0) 1
  have a2 := congrFun (congrFun hA 1) 0
  have a3 := congrFun (congrFun hA 1) 1
  have b0 := congrFun (congrFun hB 0) 0
  have b1 := congrFun (congrFun hB 0) 1
  have b2 := congrFun (congrFun hB 1) 0
  have b3 := congrFun (congrFun hB 1) 1
  simp only [blkA, blkB, mkM, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at a0 a1 a2 a3 b0 b1 b2 b3
  have hxn := (isNorm_iff x).1 (((validE_iff x).1 hx).1)
  have hyn := (isNorm_iff y).1 (((validE_iff y).1 hy).1)
  have hc1 : c = 1 := by
    rcases hxn with hx0 | ⟨hx0, hx1⟩
    · rw [hx0, cF_one, mul_one] at a0
      rcases hyn with hy0 | ⟨hy0, hy1⟩
      · rw [hy0, cF_one] at a0
        exact a0.symm
      · rw [hy0, cF_zero] at a0
        exact absurd a0.symm hc
    · rw [hx0, cF_zero, mul_zero] at a0
      have hy0 : y.a0 = 0 := cF_eq_zero.1 a0
      rcases hyn with hy0' | ⟨-, hy1⟩
      · rw [hy0] at hy0'
        exact absurd hy0' (by decide)
      · rw [hy1, hx1, cF_one, mul_one] at a1
        exact a1.symm
  rw [hc1, one_mul] at a0 a1 a2 a3 b0 b1 b2 b3
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, xs⟩ := x
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, ys⟩ := y
  simp only at a0 a1 a2 a3 b0 b1 b2 b3 hs
  rw [E.mk.injEq]
  exact ⟨(cF_injective a0).symm, (cF_injective a1).symm, (cF_injective a2).symm, (cF_injective a3).symm,
    (cF_injective b0).symm, (cF_injective b1).symm, (cF_injective b2).symm, (cF_injective b3).symm, hs.symm⟩

omit [CharP F 5] in
theorem mat4_mul_scalar (M : Matrix (Fin 4) (Fin 4) F) (c : F) : M * Matrix.scalar (Fin 4) c = c • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem ιF_inj {x y : E} (hx : validE x = true) (hy : validE y = true) (h : ιF F x = ιF F y) : x = y := by
  rw [ιF_eq hx, ιF_eq hy, mkP_eq_iff] at h
  obtain ⟨c, hc⟩ := h
  have h1 : glE y = glE x * Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
    have h2 := congrArg (fun g => glE x * g) hc
    simpa using h2
  refine eq_of_mat4_smul hx hy (c : F) ?_
  have h2 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h1
  simp only [Units.val_mul, coe_glE hx, coe_glE hy, Matrix.GeneralLinearGroup.coe_scalar] at h2
  rw [h2, mat4_mul_scalar]

theorem model_ιF : Model (ιF F) where
  valid_one := valid_oneE
  valid_mul := fun _ _ hx hy => validE_mulE hx hy
  valid_inv := fun _ hx => validE_invE hx
  map_one := ιF_one
  map_mul := fun _ _ hx hy => ιF_mul hx hy
  map_inv := fun _ hx => ιF_inv hx
  inj := fun _ _ hx hy h => ιF_inj hx hy h

end CFSG.GH74.GLS.LU.Local.FiveStd.Mat
