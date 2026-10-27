module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3A
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem exists_conj_eq_smul {g : GL (Fin 3) K} {x y : SL(3, K)}
    (h : conjAut 3 K g (proj 3 K x) = proj 3 K y) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (ω : K) • (y : Matrix (Fin 3) (Fin 3) K) := by
  rw [conjAut_proj, proj_eq_proj_iff] at h
  obtain ⟨c, hc3, hc⟩ := mem_scalars.mp h
  refine ⟨c⁻¹, by rw [inv_pow, hc3, inv_one], ?_⟩
  set A := ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K g x with hA
  have hy : (y : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) (c : K) := by
    have e : y = A * (A⁻¹ * y) := (mul_inv_cancel_left A y).symm
    rw [← hc]
    conv_lhs => rw [e]
    rfl
  rw [← coe_slConjugation, ← hA, hy, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_smul]

theorem coe_blkP_scalar {l : Kˣ} (hl : (l : K) * l = -1) :
    ((blkP 1 (GeneralLinearGroup.scalar (Fin 2) l) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(l : K), l, -1] := by
  rw [coe_blkP_one, GeneralLinearGroup.coe_scalar]
  have hdet : (scalar (Fin 2) (l : K)).det = -1 := by
    rw [Matrix.det_fin_two]; simp [hl]
  rw [hdet]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]

theorem trace_sq_diag {l : K} (hl : l * l = -1) :
    trace (diagonal ![l, l, -1] * diagonal ![l, l, -1]) = -1 := by
  rw [diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_three]
  simp [hl]

theorem eq_one_of_sq_trace {ω : Kˣ} (h3 : ω ^ 3 = 1) (h : (-1 : K) = (ω : K) ^ 2 * -1) :
    ω = 1 := by
  have h2 : ω ^ 2 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination h)
  exact Q5GL2.eq_one_of_sq_of_cube h2 h3

theorem not_fix_dual (h2 : (2 : K) ≠ 0) {l : Kˣ} (hl : (l : K) * l = -1) (g : GL (Fin 3) K) :
    (conjAut 3 K g * dualAut 3 K) (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) ≠
      proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l)) := by
  intro h
  rw [MulAut.mul_apply, dualAut_proj, ← map_inv, ← map_inv] at h
  obtain ⟨ω, hω3, hω⟩ := exists_conj_eq_smul h
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hinv : ((l⁻¹ : Kˣ) : K) = -l := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right (by linear_combination -hl)
  have hl' : ((l⁻¹ : Kˣ) : K) * (l⁻¹ : Kˣ) = -1 := by rw [hinv]; linear_combination hl
  have hx : (((blkP 1 (GeneralLinearGroup.scalar (Fin 2) l⁻¹)).transpose : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![-(l : K), -l, -1] := by
    rw [SpecialLinearGroup.coe_transpose, coe_blkP_scalar hl', diagonal_transpose, hinv]
  rw [hx, coe_blkP_scalar hl] at hω
  obtain ⟨htr, htr2⟩ := MF163.trace_eq_of_conj hω
  have hsq : diagonal ![-(l : K), -l, -1] = diagonal ![-(l : K), -l, -1] := rfl
  have h1 : trace (diagonal ![-(l : K), -l, -1] * diagonal ![-(l : K), -l, -1]) = -1 := by
    rw [diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_three]
    simp
    linear_combination 2 * hl
  rw [h1, trace_sq_diag hl] at htr2
  have hω1 := eq_one_of_sq_trace hω3 htr2
  rw [hω1, Units.val_one, one_mul, trace_diagonal, trace_diagonal, Fin.sum_univ_three,
    Fin.sum_univ_three] at htr
  simp at htr
  have h4 : (4 : K) * l = 0 := by linear_combination -htr
  have h4' : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  exact hl0 ((mul_eq_zero.1 h4).resolve_left h4')

theorem block_of_fix (h2 : (2 : K) ≠ 0) {l : Kˣ} (hl : (l : K) * l = -1) {g : GL (Fin 3) K}
    (h : conjAut 3 K g (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) =
      proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) :
    (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  obtain ⟨ω, hω3, hω⟩ := exists_conj_eq_smul h
  rw [coe_blkP_scalar hl] at hω
  have htr2 := (MF163.trace_eq_of_conj hω).2
  rw [trace_sq_diag hl] at htr2
  rw [eq_one_of_sq_trace hω3 htr2, Units.val_one, one_smul] at hω
  have hcomm : (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![(l : K), l, -1] =
      diagonal ![(l : K), l, -1] * g := by
    calc (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![(l : K), l, -1]
        = (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![(l : K), l, -1] *
            (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = diagonal ![(l : K), l, -1] * g := by rw [← Matrix.mul_assoc, hω]
  have hl1 : (l : K) ≠ -1 := fun h1 => h2 (by rw [h1] at hl; linear_combination hl)
  exact MF163.block_of_commute_diag hl1 hcomm

theorem det_eq_of_comm [Finite K] (μ : Kˣ) {g : GL (Fin 3) K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (h : conjAut 3 K g * (conjAut 3 K (sigMat μ) * dualAut 3 K) =
      conjAut 3 K (sigMat μ) * dualAut 3 K * conjAut 3 K g) :
    (g : Matrix (Fin 3) (Fin 3) K) 0 0 * (g : Matrix (Fin 3) (Fin 3) K) 1 1 -
        (g : Matrix (Fin 3) (Fin 3) K) 0 1 * (g : Matrix (Fin 3) (Fin 3) K) 1 0 =
      (g : Matrix (Fin 3) (Fin 3) K) 2 2 * (g : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  obtain ⟨h02, h12, h20, h21⟩ := hg
  rw [← mul_assoc, ← map_mul, mul_assoc, dualAut_mul_conjAut, ← mul_assoc, ← map_mul] at h
  have h1 := mul_right_cancel h
  have h3 : conjAut 3 K ((sigMat μ * GeneralLinearGroup.inverseTranspose g)⁻¹ *
      (g * sigMat μ)) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨κ, hκ⟩ := (conjAut_eq_one_iff (le_refl 3) _).1 h3
  have hgM : g * sigMat μ = sigMat μ * GeneralLinearGroup.inverseTranspose g *
      GeneralLinearGroup.scalar (Fin 3) κ := by
    rw [← hκ, mul_inv_cancel_left]
  have hmat : (g : Matrix (Fin 3) (Fin 3) K) * (sigMat μ : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K)ᵀ = (κ : K) • (sigMat μ : Matrix (Fin 3) (Fin 3) K) := by
    have e := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K)ᵀ) hgM
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at e
    rw [e, GeneralLinearGroup.coe_inverseTranspose, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one]
  have e01 := congrFun (congrFun hmat 0) 1
  have e22 := congrFun (congrFun hmat 2) 2
  rw [coe_sigMat] at e01 e22
  simp [Lemma41aL3.blkMat, jMat, Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20,
    h21] at e01 e22
  have hμ : (μ : K) ≠ 0 := μ.ne_zero
  have hdet : (g : Matrix (Fin 3) (Fin 3) K) 0 0 * (g : Matrix (Fin 3) (Fin 3) K) 1 1 -
      (g : Matrix (Fin 3) (Fin 3) K) 0 1 * (g : Matrix (Fin 3) (Fin 3) K) 1 0 = κ := by
    have : ((g : Matrix (Fin 3) (Fin 3) K) 0 0 * (g : Matrix (Fin 3) (Fin 3) K) 1 1 -
      (g : Matrix (Fin 3) (Fin 3) K) 0 1 * (g : Matrix (Fin 3) (Fin 3) K) 1 0 - κ) * μ = 0 := by
      linear_combination -e01
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hμ)
  rw [hdet]
  linear_combination -e22

end CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
