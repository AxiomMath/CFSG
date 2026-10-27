module

public import CFSG.GH74.GLS.LU.Local.FiveStdMat2
public import CFSG.GH74.GLS.Stage2.Final.ModelBlock

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd.Mat

open CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock Matrix

variable {F : Type} [Field F] [CharP F 5]

open scoped Classical in
@[expose] noncomputable def glE (x : E) : GL (Fin 4) F :=
  if h : (mat4 x : Matrix (Fin 4) (Fin 4) F).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero (mat4 x) h
  else 1

theorem det_mat4_valid {x : E} (hx : validE x = true) :
    (mat4 x : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [det_mat4, ((validE_iff x).1 hx).2, cF_one]

theorem coe_glE {x : E} (hx : validE x = true) :
    ((glE x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = mat4 x := by
  have h : (mat4 x : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by
    rw [det_mat4_valid hx]
    exact one_ne_zero
  simp only [glE, h, ne_eq, not_false_eq_true, ↓reduceDIte]
  rfl

theorem glE_mem_K4 {x : E} (hx : validE x = true) : glE x ∈ (ModelData.lin F).K4 :=
  ((ModelData.lin F).mem_K4 _).2 ⟨Subgroup.mem_top _, by rw [coe_glE hx]; exact det_mat4_valid hx⟩

@[expose] noncomputable def ιF (F : Type) [Field F] [CharP F 5] (x : E) : PG (ModelData.lin F) :=
  if h : validE x = true then mkP (ModelData.lin F) ⟨glE x, glE_mem_K4 h⟩ else 1

theorem ιF_eq {x : E} (hx : validE x = true) :
    ιF F x = mkP (ModelData.lin F) ⟨glE x, glE_mem_K4 hx⟩ := by
  simp only [ιF, hx, ↓reduceDIte]

theorem cF_ne_zero_unit {c : Fin 5} (hc : c ≠ 0) : cF F c ≠ 0 := fun h => hc (cF_eq_zero.1 h)

omit [CharP F 5] in
theorem scalar_mul_mat (c : F) (M : Matrix (Fin 4) (Fin 4) F) : Matrix.scalar (Fin 4) c * M = c • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem glE_mulE {x y : E} (hx : validE x = true) (hy : validE y = true) :
    ∃ u : Fˣ, glE (mulE x y) = Matrix.GeneralLinearGroup.scalar (Fin 4) u * (glE x * glE y) := by
  have hxy := validE_mulE hx hy
  have hc : cF F (cn (mulRaw x y)) ≠ 0 := by
    apply cF_ne_zero_unit
    obtain ⟨hxA, hxB⟩ := det_ne_zero_of_valid hx
    obtain ⟨hyA, hyB⟩ := det_ne_zero_of_valid hy
    apply cn_ne_zero
    cases hs : x.s
    · rw [detA_mulRaw_of_false y hs]
      exact mul_ne_zero_fin5 _ _ hxA hyA
    · rw [detA_mulRaw_of_true y hs]
      exact mul_ne_zero_fin5 _ _ hxA hyB
  refine ⟨Units.mk0 _ hc, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_glE hxy, coe_glE hx,
    coe_glE hy, scalar_mul_mat, mat4_mulE]
  rfl

theorem glE_mul_invE {x : E} (hx : validE x = true) :
    ∃ u : Fˣ, glE x * glE (invE x) = Matrix.GeneralLinearGroup.scalar (Fin 4) u := by
  have hi := validE_invE hx
  have hc : cF F (cn (invRaw x)) ≠ 0 := by
    apply cF_ne_zero_unit
    obtain ⟨hxA, hxB⟩ := det_ne_zero_of_valid hx
    apply cn_ne_zero
    cases hs : x.s
    · rw [detA_invRaw_false hx hs]
      exact inv5_ne_zero _ hxA
    · rw [detA_invRaw_true hx hs]
      exact inv5_ne_zero _ hxB
  refine ⟨Units.mk0 _ hc, Units.ext ?_⟩
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_glE hi, coe_glE hx, mat4_mul_invE hx]
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rfl

theorem valid_oneE : validE oneE = true := by decide

theorem mkM_one : (mkM 1 0 0 1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkM, cF_zero, cF_one]

theorem mat4_oneE : (mat4 oneE : Matrix (Fin 4) (Fin 4) F) = 1 := by
  simp only [mat4, oneE, blkA, blkB, mkM_one, blk4_one]
  simp

theorem glE_oneE : (glE oneE : GL (Fin 4) F) = 1 :=
  Units.ext (by rw [coe_glE valid_oneE, mat4_oneE]; rfl)

theorem ιF_one : ιF F oneE = 1 := by
  rw [ιF_eq valid_oneE]
  have : (⟨glE oneE, glE_mem_K4 valid_oneE⟩ : ↥(ModelData.lin F).K4) = 1 := Subtype.ext glE_oneE
  rw [this, map_one]

omit [CharP F 5] in
theorem inv_scalar_mul_cancel (u : Fˣ) (P : GL (Fin 4) F) :
    (Matrix.GeneralLinearGroup.scalar (Fin 4) u * P)⁻¹ * P =
      Matrix.GeneralLinearGroup.scalar (Fin 4) u⁻¹ := by
  rw [_root_.mul_inv_rev, ← map_inv]
  calc P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 4) u⁻¹ * P
      = P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 4) u⁻¹ * P) := by rw [mul_assoc]
    _ = P⁻¹ * (P * Matrix.GeneralLinearGroup.scalar (Fin 4) u⁻¹) := by
        rw [Matrix.GeneralLinearGroup.scalar_commute]
    _ = Matrix.GeneralLinearGroup.scalar (Fin 4) u⁻¹ := by rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem ιF_mul {x y : E} (hx : validE x = true) (hy : validE y = true) :
    ιF F (mulE x y) = ιF F x * ιF F y := by
  have hxy := validE_mulE hx hy
  obtain ⟨u, hu⟩ := glE_mulE (F := F) hx hy
  rw [ιF_eq hxy, ιF_eq hx, ιF_eq hy, ← map_mul, mkP_eq_iff]
  refine ⟨u⁻¹, ?_⟩
  show (glE (mulE x y))⁻¹ * (glE x * glE y) = _
  rw [hu]
  exact inv_scalar_mul_cancel u _

theorem ιF_inv {x : E} (hx : validE x = true) : ιF F (invE x) = (ιF F x)⁻¹ := by
  have hi := validE_invE hx
  obtain ⟨u, hu⟩ := glE_mul_invE (F := F) hx
  refine eq_inv_of_mul_eq_one_right ?_
  rw [ιF_eq hx, ιF_eq hi, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_Zs]
  exact ⟨u, hu.symm⟩

end CFSG.GH74.GLS.LU.Local.FiveStd.Mat
