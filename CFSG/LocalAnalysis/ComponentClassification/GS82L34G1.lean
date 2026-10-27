module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1LnAut
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.ComponentClassification.GSThmB.L34DP

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

@[expose] noncomputable def blk (a b : SL(2, ZMod 7)) : SL(4, ZMod 7) :=
  ⟨Matrix.reindex (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) finSumFinEquiv
      (Matrix.fromBlocks (a : Matrix (Fin 2) (Fin 2) (ZMod 7)) 0 0 (b : Matrix (Fin 2) (Fin 2) (ZMod 7))), by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, a.2, b.2, mul_one]⟩

@[expose] def dSL : SL(4, ZMod 7) := ⟨Matrix.diagonal ![-1, -1, 1, 1], by decide⟩

@[expose] def lowL : SL(2, ZMod 7) := ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩

theorem coe_blk_low_one : ((blk lowL 1 : SL(4, ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7)) =
    !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coe_blk_one_low : ((blk 1 lowL : SL(4, ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7)) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem fieldAut_seven (σ : ZMod 7 ≃+* ZMod 7) : fieldAut 4 (ZMod 7) σ = 1 := by
  have hσ : σ = 1 := RingEquiv.ext fun x =>
    congrArg (fun f : ZMod 7 →+* ZMod 7 => f x)
      (RingHom.ext_zmod (σ : ZMod 7 →+* ZMod 7) (RingHom.id _))
  rw [hσ, map_one]

theorem conj_proj_eq (d : SL(4, ZMod 7)) :
    MulAut.conj (proj 4 (ZMod 7) d) =
      conjAut 4 (ZMod 7) (Matrix.SpecialLinearGroup.toGL d) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective 4 (ZMod 7) x
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg (proj 4 (ZMod 7)) ?_
  apply Subtype.ext
  rw [coe_slConjugation, ← map_inv]
  rfl

theorem four_eq (c : ZMod 7) (h : (4 : ZMod 7) = c * 4) : c = 1 := by
  revert c h; decide

theorem fix_eq {A : GL (Fin 4) (ZMod 7)} {x y : SL(4, ZMod 7)}
    (h : conjAut 4 (ZMod 7) A (proj 4 (ZMod 7) y) = proj 4 (ZMod 7) x)
    (hx : (x : Matrix (Fin 4) (Fin 4) (ZMod 7)).trace = 4)
    (hy : (y : Matrix (Fin 4) (Fin 4) (ZMod 7)).trace = 4) :
    (x : Matrix (Fin 4) (Fin 4) (ZMod 7)) * (A : Matrix (Fin 4) (Fin 4) (ZMod 7)) =
      (A : Matrix (Fin 4) (Fin 4) (ZMod 7)) * y := by
  rw [conjAut_proj] at h
  obtain ⟨c, -, hc⟩ := GH74.GLS.Stage2.Signalizer.Ivk8.exists_smul_of_proj_eq h
  rw [coe_slConjugation] at hc
  have hinv : ((A⁻¹ : GL (Fin 4) (ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7)) * A = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr : ((A : Matrix (Fin 4) (Fin 4) (ZMod 7)) * y *
      ((A⁻¹ : GL (Fin 4) (ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7))).trace = 4 := by
    rw [Matrix.trace_mul_cycle, hinv, Matrix.one_mul, hy]
  have hc1 : c = 1 := by
    have := congrArg Matrix.trace hc
    rw [Matrix.trace_smul, htr, hx, smul_eq_mul] at this
    exact four_eq c this
  rw [hc, hc1, one_smul, Matrix.mul_assoc, hinv, Matrix.mul_one]

theorem coe_dSL : ((dSL : SL(4, ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7)) =
    Matrix.diagonal ![-1, -1, 1, 1] := by rfl

theorem sum_sq_seven : ∀ a b : ZMod 7, a * a + b * b = 0 → b = 0 := by decide

theorem case0 (A : GL (Fin 4) (ZMod 7))
    (hα : ∀ a b : SL(2, ZMod 7),
      conjAut 4 (ZMod 7) A (proj 4 (ZMod 7) (blk a b)) = proj 4 (ZMod 7) (blk a b))
    (h2 : conjAut 4 (ZMod 7) A * conjAut 4 (ZMod 7) A = MulAut.conj (proj 4 (ZMod 7) dSL)) :
    False := by
  have e1 := fix_eq (hα lowL 1) (by rw [coe_blk_low_one]; norm_num [Matrix.trace, Fin.sum_univ_four])
    (by rw [coe_blk_low_one]; norm_num [Matrix.trace, Fin.sum_univ_four])
  have e2 := fix_eq (hα 1 lowL) (by rw [coe_blk_one_low]; norm_num [Matrix.trace, Fin.sum_univ_four])
    (by rw [coe_blk_one_low]; norm_num [Matrix.trace, Fin.sum_univ_four])
  rw [coe_blk_low_one] at e1
  rw [coe_blk_one_low] at e2
  have a01 := congrFun (congrFun e1 1) 1
  have a02 := congrFun (congrFun e1 1) 2
  have a03 := congrFun (congrFun e1 1) 3
  have a20 := congrFun (congrFun e2 3) 0
  have a21 := congrFun (congrFun e2 3) 1
  have a23 := congrFun (congrFun e2 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at a01 a02 a03 a20 a21 a23
  rw [← map_mul, conj_proj_eq] at h2
  have h3 : conjAut 4 (ZMod 7) (A * A * (Matrix.SpecialLinearGroup.toGL dSL)⁻¹) = 1 := by
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  obtain ⟨c, hc⟩ := GH74.GLS.Stage2.Bender.Thm1.Ln.eq_scalar_of_conjAut_eq_one (by norm_num) h3
  have h4 := mul_inv_eq_iff_eq_mul.mp hc.symm
  have f00 := congrArg (fun U : GL (Fin 4) (ZMod 7) => (U : Matrix (Fin 4) (Fin 4) (ZMod 7)) 0 0) h4
  have f22 := congrArg (fun U : GL (Fin 4) (ZMod 7) => (U : Matrix (Fin 4) (Fin 4) (ZMod 7)) 2 2) h4
  simp [Matrix.mul_apply, Fin.sum_univ_four, coe_dSL, GeneralLinearGroup.coe_scalar,
    a01, a02, a03, a20, a21, a23] at f00 f22
  have h5 := sum_sq_seven ((A : Matrix (Fin 4) (Fin 4) (ZMod 7)) 0 0)
    ((A : Matrix (Fin 4) (Fin 4) (ZMod 7)) 2 2) (by rw [f00, f22]; ring)
  rw [h5, mul_zero] at f22
  exact c.ne_zero f22.symm

theorem coe_inv_of_mul {x : SL(4, ZMod 7)} {M : Matrix (Fin 4) (Fin 4) (ZMod 7)}
    (h : (x : Matrix (Fin 4) (Fin 4) (ZMod 7)) * M = 1) :
    ((x⁻¹ : SL(4, ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7)) = M := by
  calc ((x⁻¹ : SL(4, ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7))
      = ((x⁻¹ : SL(4, ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7)) *
          ((x : Matrix (Fin 4) (Fin 4) (ZMod 7)) * M) := by rw [h, Matrix.mul_one]
    _ = M := by
      have hx : ((x⁻¹ : SL(4, ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7)) * x = 1 :=
        congr_arg (·.1) (inv_mul_cancel x)
      rw [← Matrix.mul_assoc, hx, Matrix.one_mul]

theorem coe_dual_low_one :
    (((blk lowL 1)⁻¹.transpose : SL(4, ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7)) =
      !![1, -1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  have hm : (!![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) (ZMod 7)) *
      !![1, 0, 0, 0; -1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  rw [← coe_blk_low_one] at hm
  rw [SpecialLinearGroup.coe_transpose, coe_inv_of_mul hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_dual_one_low :
    (((blk 1 lowL)⁻¹.transpose : SL(4, ZMod 7)) : Matrix (Fin 4) (Fin 4) (ZMod 7)) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, -1; 0, 0, 0, 1] := by
  have hm : (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, 1] : Matrix (Fin 4) (Fin 4) (ZMod 7)) *
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, -1, 1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  rw [← coe_blk_one_low] at hm
  rw [SpecialLinearGroup.coe_transpose, coe_inv_of_mul hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem case1_final : ∀ c p q : ZMod 7, p ≠ 0 → q ≠ 0 → -p = -(c * p) → -q = c * q → False := by
  decide

theorem case1 (A : GL (Fin 4) (ZMod 7))
    (hα : ∀ a b : SL(2, ZMod 7), (conjAut 4 (ZMod 7) A * dualAut 4 (ZMod 7))
      (proj 4 (ZMod 7) (blk a b)) = proj 4 (ZMod 7) (blk a b))
    (h2 : conjAut 4 (ZMod 7) A * dualAut 4 (ZMod 7) * (conjAut 4 (ZMod 7) A * dualAut 4 (ZMod 7)) =
      MulAut.conj (proj 4 (ZMod 7) dSL)) :
    False := by
  have hf : ∀ a b : SL(2, ZMod 7), conjAut 4 (ZMod 7) A (proj 4 (ZMod 7) (blk a b)⁻¹.transpose) =
      proj 4 (ZMod 7) (blk a b) := by
    intro a b
    have := hα a b
    rwa [MulAut.mul_apply, dualAut_proj] at this
  have e1 := fix_eq (hf lowL 1)
    (by rw [coe_blk_low_one]; norm_num [Matrix.trace, Fin.sum_univ_four])
    (by rw [coe_dual_low_one]; norm_num [Matrix.trace, Fin.sum_univ_four])
  have e2 := fix_eq (hf 1 lowL)
    (by rw [coe_blk_one_low]; norm_num [Matrix.trace, Fin.sum_univ_four])
    (by rw [coe_dual_one_low]; norm_num [Matrix.trace, Fin.sum_univ_four])
  rw [coe_blk_low_one, coe_dual_low_one] at e1
  rw [coe_blk_one_low, coe_dual_one_low] at e2
  have a00 := congrFun (congrFun e1 1) 0
  have a01 := congrFun (congrFun e1 1) 1
  have a02 := congrFun (congrFun e1 1) 2
  have a03 := congrFun (congrFun e1 1) 3
  have a20 := congrFun (congrFun e2 3) 0
  have a21 := congrFun (congrFun e2 3) 1
  have a22 := congrFun (congrFun e2 3) 2
  have a23 := congrFun (congrFun e2 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at a00 a01 a02 a03 a20 a21 a22 a23
  have hdc := (standard_automorphism_transport
    (n := 4) (K := ZMod 7)).2.2.2.2.1 A
  have h2' : conjAut 4 (ZMod 7) (A * GeneralLinearGroup.inverseTranspose A) =
      conjAut 4 (ZMod 7) (Matrix.SpecialLinearGroup.toGL dSL) := by
    rw [← conj_proj_eq, ← h2, map_mul, ← hdc]
    simp only [mul_assoc]
  have h3 : conjAut 4 (ZMod 7) (A * GeneralLinearGroup.inverseTranspose A *
      (Matrix.SpecialLinearGroup.toGL dSL)⁻¹) = 1 := by
    rw [map_mul, map_inv, h2', mul_inv_cancel]
  obtain ⟨c, hc⟩ := GH74.GLS.Stage2.Bender.Thm1.Ln.eq_scalar_of_conjAut_eq_one (by norm_num) h3
  have h4 := eq_mul_inv_of_mul_eq (mul_inv_eq_iff_eq_mul.mp hc.symm)
  have hIT : ((GeneralLinearGroup.inverseTranspose A)⁻¹ : GL (Fin 4) (ZMod 7)) =
      (A : Matrix (Fin 4) (Fin 4) (ZMod 7))ᵀ := by
    rw [← map_inv, GeneralLinearGroup.coe_inverseTranspose, inv_inv]
  have h5 := congrArg (fun U : GL (Fin 4) (ZMod 7) => (U : Matrix (Fin 4) (Fin 4) (ZMod 7))) h4
  simp only [Units.val_mul, hIT, SpecialLinearGroup.coe_GL_coe_matrix,
    GeneralLinearGroup.coe_scalar, coe_dSL] at h5
  have f01 := congrFun (congrFun h5 0) 1
  have f10 := congrFun (congrFun h5 1) 0
  have f23 := congrFun (congrFun h5 2) 3
  have f32 := congrFun (congrFun h5 3) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four] at f01 f10 f23 f32
  have hdet : (A : Matrix (Fin 4) (Fin 4) (ZMod 7)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A)).ne_zero
  have hp : (A : Matrix (Fin 4) (Fin 4) (ZMod 7)) 1 0 ≠ 0 := fun h =>
    hdet (Matrix.det_eq_zero_of_row_eq_zero 0 fun j => by
      fin_cases j <;> simp [a00, a01, a02, a03, h])
  have hq : (A : Matrix (Fin 4) (Fin 4) (ZMod 7)) 3 2 ≠ 0 := fun h =>
    hdet (Matrix.det_eq_zero_of_row_eq_zero 2 fun j => by
      fin_cases j <;> simp [a20, a21, a22, a23, h])
  rw [a01] at f01
  rw [a23] at f23
  exact case1_final _ _ _ hp hq f01 f23

theorem g1_no_sqrt (α : MulAut (projectiveSL 4 (ZMod 7)))
    (hα : ∀ a b : SL(2, ZMod 7), α (proj 4 (ZMod 7) (blk a b)) = proj 4 (ZMod 7) (blk a b)) :
    α * α ≠ MulAut.conj (proj 4 (ZMod 7) dSL) := by
  intro h2
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := ZMod 7) (n := 4) (by norm_num)).2 α
  rw [fieldAut_seven, mul_one] at hα h2
  interval_cases ε
  · rw [pow_zero, mul_one] at hα h2
    exact case0 A hα h2
  · rw [pow_one] at hα h2
    exact case1 A hα h2

end CFSG.ComponentClassification.GSThmB.L34DP
