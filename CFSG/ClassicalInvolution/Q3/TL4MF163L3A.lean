module

public import CFSG.ClassicalInvolution.Q3.TL4MF163LUM
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Frame
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def sigMat (μ : Kˣ) : GL (Fin 3) K where
  val := Lemma41aL3.blkMat (jMat (μ : K)) 1
  inv := Lemma41aL3.blkMat (jMat (-(μ⁻¹ : Kˣ) : K)) 1
  val_inv := by rw [Lemma41aL3.blkMat_mul, jMat_mul_jMat_inv, one_mul, Lemma41aL3.blkMat_one]
  inv_val := by rw [Lemma41aL3.blkMat_mul, jMat_inv_mul_jMat, one_mul, Lemma41aL3.blkMat_one]

theorem coe_sigMat (μ : Kˣ) :
    ((sigMat μ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Lemma41aL3.blkMat (jMat (μ : K)) 1 := rfl

theorem coe_sigMat_inv (μ : Kˣ) :
    (((sigMat μ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Lemma41aL3.blkMat (jMat (-(μ⁻¹ : Kˣ) : K)) 1 := rfl

theorem coe_blkP_one (A : GL (Fin 2) K) :
    ((blkP 1 A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      Lemma41aL3.blkMat (A : Matrix (Fin 2) (Fin 2) K) (A : Matrix (Fin 2) (Fin 2) K).det⁻¹ := by
  show ((1 * Lemma41aL3.blk A * 1⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
  rw [one_mul, inv_one, mul_one, Lemma41aL3.coe_blk]

theorem sig_dual_blkP (μ : Kˣ) (A : GL (Fin 2) K) :
    (conjAut 3 K (sigMat μ) * dualAut 3 K) (proj 3 K (blkP 1 A)) =
      proj 3 K (blkP 1 (A * GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det A)⁻¹)) := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj, ← map_inv]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, SpecialLinearGroup.coe_transpose, coe_blkP_one, coe_blkP_one,
    coe_sigMat, coe_sigMat_inv, blkMat_transpose, Lemma41aL3.blkMat_mul, Lemma41aL3.blkMat_mul,
    jMat_inv_transpose]
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := Lemma41aL3.det_ne_zero_gl A
  congr 1
  · rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val,
      GeneralLinearGroup.val_det_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  · rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.det_mul, Matrix.coe_units_inv,
      Matrix.det_nonsing_inv]
    simp [Matrix.det_fin_two, GeneralLinearGroup.val_det_apply]
    field_simp

theorem fix_sig_one (B : SL(2, K)) :
    (conjAut 3 K (sigMat 1) * dualAut 3 K) (proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))) =
      proj 3 K (blkP 1 (SpecialLinearGroup.toGL B)) := by
  rw [sig_dual_blkP, SpecialLinearGroup.coeToGL_det, inv_one, map_one, mul_one]

end CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
