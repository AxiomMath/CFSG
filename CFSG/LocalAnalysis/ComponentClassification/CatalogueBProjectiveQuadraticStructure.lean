module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

open CatalogueBProjectiveInvolution

variable {K : Type*} [Field K]

theorem nonsquare_matrix_dimension (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda)
    (hns : ¬ IsSquare lambda.val) :
    letI : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
    letI := matrixModule A lambda hsq
    n = 2 * Module.finrank (extension lambda.val) (Fin n → K) ∧
      1 ≤ Module.finrank (extension lambda.val) (Fin n → K) := by
  let : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  exact ⟨by simpa only [Fintype.card_fin, matrixDimension] using
    matrixDimension_twice A lambda hsq, matrixDimension_pos A lambda hsq⟩

theorem nonsquare_projective_centralizer_structure (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda)
    (hns : ¬ IsSquare lambda.val) :
    let E := extension lambda.val
    letI : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
    letI := matrixModule A lambda hsq
    let m := Module.finrank E (Fin n → K)
    IsField E ∧ Module.finrank K E = 2 ∧ n = 2 * m ∧ 1 ≤ m ∧
      IsScalarTower K E (Fin n → K) ∧ Module.Finite E (Fin n → K) ∧
      (∀ v : Fin n → K,
        AdjoinRoot.root (quadraticPolynomial lambda.val) • v = A.val.mulVec v) ∧
      (∀ (c : K) (v : Fin n → K), algebraMap K E c • v = c • v) ∧
      (∀ L : Module.End K (Fin n → K), Commute L (matrixOperator A) ↔
        ∀ (x : E) (v : Fin n → K), L (x • v) = x • L v) ∧
      ∃ (phi : E →ₐ[K] Module.End K (Fin n → K))
        (b : Module.Basis (Fin m) E (Fin n → K))
        (e : Subgroup.centralizer {A} ≃* Matrix.GeneralLinearGroup (Fin m) E)
        (q : (ordinaryCentralizerProjection A).range ≃*
          (Matrix.GeneralLinearGroup (Fin m) E ⧸ (matrixKScalars lambda.val m).range)),
        Function.Injective phi ∧
        phi (AdjoinRoot.root (quadraticPolynomial lambda.val)) = matrixOperator A ∧
        phi.range = Algebra.adjoin K {matrixOperator A} ∧
        (∀ c : K, phi (algebraMap K E c) =
          algebraMap K (Module.End K (Fin n → K)) c) ∧
        (∀ (B : Subgroup.centralizer {A}) (v : Fin n → K),
          (e B).val.mulVec (b.equivFun v) = b.equivFun (B.val.val.mulVec v)) ∧
        (∀ c : Kˣ, e (ordinaryCentralizerScalar A c) =
          Matrix.GeneralLinearGroup.scalar (Fin m)
            (Units.map (algebraMap K E).toMonoidHom c)) ∧
        (∀ B : Subgroup.centralizer {A},
          q ⟨ordinaryCentralizerProjection A B, ⟨B, rfl⟩⟩ = QuotientGroup.mk (e B)) := by
  let : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let := matrixModule A lambda hsq
  obtain ⟨hdim, hpos⟩ := nonsquare_matrix_dimension n hn A lambda hsq hns
  refine ⟨extension_isField lambda.val hns, extension_finrank lambda.val, hdim, hpos,
    matrixModule_scalarTower A lambda hsq, matrixModule_finite A lambda hsq,
    matrixModule_root_smul A lambda hsq, matrixModule_algebraMap_smul A lambda hsq,
    commute_iff_action_linear (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq),
    actionHom (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq),
    matrixBasis A lambda hsq, matrixCentralizerQuadraticEquiv A lambda hsq,
    projectiveQuadraticQuotientEquiv A lambda hsq,
    actionHom_injective (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq),
    actionHom_root (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq),
    actionHom_range (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq),
    actionHom_algebraMap (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq),
    matrixCentralizerQuadraticEquiv_mulVec A lambda hsq,
    matrixCentralizerQuadraticEquiv_scalar A lambda hsq,
    projectiveQuadraticQuotientEquiv_projection A lambda hsq⟩

end CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
