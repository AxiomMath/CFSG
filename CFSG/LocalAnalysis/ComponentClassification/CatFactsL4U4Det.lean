module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticStructure
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix Polynomial CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

variable {F : Type*} [Field F]

theorem norm_root_quadratic (l : F) [Fact (¬ IsSquare l)] :
    Algebra.norm F (AdjoinRoot.root (quadraticPolynomial l)) = -l := by
  have hne : quadraticPolynomial l ≠ 0 := (quadraticPolynomial_monic l).ne_zero
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (AdjoinRoot.powerBasis hne)
  rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root hne,
    (quadraticPolynomial_monic l).leadingCoeff, inv_one, map_one, mul_one] at h
  rw [h, AdjoinRoot.powerBasis_dim, quadraticPolynomial_natDegree]
  simp [quadraticPolynomial]

theorem det_eq_neg_pow_of_sq_nonsquare {n : ℕ} (hn : 2 ≤ n) (A : GL (Fin n) F) (l : Fˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) l) (hns : ¬ IsSquare (l : F)) :
    (A : Matrix (Fin n) (Fin n) F).det = (-(l : F)) ^ (n / 2) := by
  have hstr := nonsquare_projective_centralizer_structure n hn A l hsq hns
  let : Fact (¬ IsSquare l.val) := ⟨hns⟩
  let := matrixModule A l hsq
  dsimp only at hstr
  obtain ⟨-, -, hm, -, htower, hfin, hroot, -, -, -⟩ := hstr
  set r := AdjoinRoot.root (quadraticPolynomial l.val) with hr
  have hlin : Matrix.toLin' (A : Matrix (Fin n) (Fin n) F) =
      ((r • LinearMap.id : (Fin n → F) →ₗ[extension l.val] (Fin n → F)).restrictScalars F) := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hroot]
  have hfree : Module.Free F (extension l.val) :=
    (quadraticPolynomial_monic l.val).free_adjoinRoot
  rw [← LinearMap.det_toLin', hlin, LinearMap.det_restrictScalars, LinearMap.det_smul,
    LinearMap.det_id, mul_one, map_pow, norm_root_quadratic]
  congr 1
  omega

theorem sq_eq_neg_one_of_det_eq_one (A : GL (Fin 4) F) (l : Fˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) l) (hns : ¬ IsSquare (l : F))
    (hdet : (A : Matrix (Fin 4) (Fin 4) F).det = 1) : (l : F) = -1 ∧ ¬ IsSquare (-1 : F) := by
  have h := det_eq_neg_pow_of_sq_nonsquare (by norm_num) A l hsq hns
  rw [hdet] at h
  have h2 : (l : F) ^ 2 = 1 := by
    have : (-(l : F)) ^ 2 = (l : F) ^ 2 := by ring
    rw [show (4 : ℕ) / 2 = 2 from rfl, this] at h
    exact h.symm
  have hl : (l : F) = 1 ∨ (l : F) = -1 := mul_self_eq_one_iff.1 (by rw [← pow_two]; exact h2)
  rcases hl with hl | hl
  · exact absurd ⟨1, by rw [hl, one_mul]⟩ hns
  · exact ⟨hl, hl ▸ hns⟩

end CFSG.ComponentClassification.CatFactsL4U4
