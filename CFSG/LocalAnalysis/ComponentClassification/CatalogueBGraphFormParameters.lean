module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFaithfulness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionCharacter

public section

namespace CFSG.ComponentClassification.CatalogueBGraphForm

noncomputable section

open CatalogueBHigherLinearAction

universe u

theorem pureGraph_involution_scalar (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 3 ≤ n) (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hsq : pureGraphAction n K A ^ 2 = 1) :
    ∃ lambda : Kˣ, A * glGraphAut n K A = Matrix.GeneralLinearGroup.scalar (Fin n) lambda := by
  obtain ⟨lambda, hlambda⟩ :=
    CatalogueBHigherLinearInner.unit_scalar_of_innerDiagonalAction_eq_one
      n K (by omega) (Or.inl hn) (A * glGraphAut n K A)
      ((pureGraphAction_sq n K A).symm.trans hsq)
  exact ⟨lambda, hlambda.symm⟩

theorem pureGraph_scalar_square (n : ℕ) (K : Type u) [Field K]
    (hn : 1 ≤ n) (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (hscalar : A * glGraphAut n K A = Matrix.GeneralLinearGroup.scalar (Fin n) lambda) :
    lambda ^ 2 = 1 := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hreverse : glGraphAut n K A * A = Matrix.GeneralLinearGroup.scalar (Fin n) lambda := by
    calc
      _ = A⁻¹ * (A * glGraphAut n K A) * A := by group
      _ = A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) lambda * A := by rw [hscalar]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) lambda := by
        rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute]
        group
  have hgraph := congrArg (glGraphAut n K) hscalar
  rw [map_mul, Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose,
    glGraphAut_scalar, hreverse] at hgraph
  have hinverse : lambda = lambda⁻¹ :=
    CatalogueBProjectiveInvolution.scalarGL_injective hgraph
  calc
    lambda ^ 2 = lambda * lambda⁻¹ := by
      rw [pow_two]
      exact congrArg (fun x => lambda * x) hinverse
    _ = 1 := mul_inv_cancel lambda

theorem pureGraph_transpose_scalar (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (hscalar : A * glGraphAut n K A = Matrix.GeneralLinearGroup.scalar (Fin n) lambda) :
    A.val.transpose = (lambda⁻¹).val • A.val := by
  have hunit : (glGraphAut n K A)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) lambda⁻¹ * A := by
    have hA : A = Matrix.GeneralLinearGroup.scalar (Fin n) lambda * (glGraphAut n K A)⁻¹ :=
      (eq_mul_inv_iff_mul_eq).mpr hscalar
    calc
      _ = (Matrix.GeneralLinearGroup.scalar (Fin n) lambda)⁻¹ * A :=
        eq_inv_mul_iff_mul_eq.mpr hA.symm
      _ = _ := by rw [← map_inv]
  have hmatrix := congrArg Units.val hunit
  rw [← map_inv, glGraphAut_matrix, inv_inv, Units.val_mul,
    Matrix.GeneralLinearGroup.coe_scalar] at hmatrix
  have hscalarMatrix : Matrix.scalar (Fin n) (lambda⁻¹).val =
      (lambda⁻¹).val • (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  rw [hscalarMatrix, Matrix.smul_mul, Matrix.one_mul] at hmatrix
  exact hmatrix

theorem pureGraph_involution_symmetric_or_skew
    (n : ℕ) (K : Type u) [Field K] [Finite K] (hn : 3 ≤ n)
    (A : Matrix.GeneralLinearGroup (Fin n) K) (hsq : pureGraphAction n K A ^ 2 = 1) :
    A.val.transpose = A.val ∨ A.val.transpose = -A.val := by
  obtain ⟨lambda, hscalar⟩ := pureGraph_involution_scalar n K hn A hsq
  have hsqLambda := pureGraph_scalar_square n K (by omega) A lambda hscalar
  have hval : lambda.val ^ 2 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hsqLambda
  have ht := pureGraph_transpose_scalar n K A lambda hscalar
  rcases sq_eq_one_iff.mp hval with h | h
  · left
    simpa [h] using ht
  · right
    simpa [h] using ht

theorem even_rank_of_skew (n : ℕ) (K : Type u) [Field K]
    (hodd : ringChar K ≠ 2) (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hskew : A.val.transpose = -A.val) : Even n := by
  have hdet : A.val.det = (-1 : K) ^ n * A.val.det := by
    calc
      _ = A.val.transpose.det := (Matrix.det_transpose _).symm
      _ = (-A.val).det := congrArg Matrix.det hskew
      _ = _ := by simpa using Matrix.det_neg A.val
  have hnonzero : A.val.det ≠ 0 := (Matrix.GeneralLinearGroup.det A).ne_zero
  have hpow : (-1 : K) ^ n = 1 :=
    mul_right_cancel₀ hnonzero (by simpa only [one_mul] using hdet.symm)
  exact (neg_one_pow_eq_one_iff_even (Ring.neg_one_ne_one_of_char_ne_two hodd)).mp hpow

theorem pureGraph_involution_form_data
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 3 ≤ n) (hodd : ringChar K ≠ 2)
    (A : Matrix.GeneralLinearGroup (Fin n) K) (hsq : pureGraphAction n K A ^ 2 = 1) :
    A.val.transpose = A.val ∨ (A.val.transpose = -A.val ∧ Even n) := by
  rcases pureGraph_involution_symmetric_or_skew n K hn A hsq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, even_rank_of_skew n K hodd A h⟩

end

end CFSG.ComponentClassification.CatalogueBGraphForm
