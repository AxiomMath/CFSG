module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticStructure

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

open CatalogueBProjectiveCoordinates CatalogueBProjectiveQuadratic

variable {K : Type*} [Field K]

@[expose] def SplitMatrixStructure (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K)
    (lambda : Kˣ) : Prop :=
  ∃ b : Kˣ, b ^ 2 = lambda ∧
    let r := positiveMatrixDimension A b.val
    let s := negativeMatrixDimension A b.val
    1 ≤ r ∧ 1 ≤ s ∧ r + s = n ∧
      ∃ (e : Subgroup.centralizer {A} ≃*
          (Matrix.GeneralLinearGroup (Fin r) K × Matrix.GeneralLinearGroup (Fin s) K))
        (q : (ordinaryCentralizerProjection A).range ≃*
          ((Matrix.GeneralLinearGroup (Fin r) K × Matrix.GeneralLinearGroup (Fin s) K) ⧸
            (splitDiagonalScalars r s).range)),
        (∀ c : Kˣ, e (ordinaryCentralizerScalar A c) =
          (Matrix.GeneralLinearGroup.scalar (Fin r) c,
            Matrix.GeneralLinearGroup.scalar (Fin s) c)) ∧
        (∀ B : Subgroup.centralizer {A},
          e B =
            (basisAutomorphismMatrixEquiv (positiveMatrixBasis A b.val)
              (operatorCentralizerRestriction (splitMatrixOperator A) b.val
                (matrixCentralizerEquiv A B)),
            basisAutomorphismMatrixEquiv (negativeMatrixBasis A b.val)
              (operatorCentralizerRestriction (splitMatrixOperator A) (-b.val)
                (matrixCentralizerEquiv A B)))) ∧
        (∀ B : Subgroup.centralizer {A},
          q ⟨ordinaryCentralizerProjection A B, ⟨B, rfl⟩⟩ = QuotientGroup.mk (e B))

@[expose] def QuadraticMatrixStructure (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K)
    (lambda : Kˣ) (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda)
    (hns : ¬ IsSquare lambda.val) : Prop :=
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
        q ⟨ordinaryCentralizerProjection A B, ⟨B, rfl⟩⟩ = QuotientGroup.mk (e B))

theorem projective_involution_centralizer_matrix_structure (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix.GeneralLinearGroup (Fin n) K) (htwo : (2 : K) ≠ 0)
    (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hinvolution : Matrix.ProjGenLinGroup.mk A ^ 2 = 1) :
    ∃ (lambda : Kˣ) (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda),
      (ordinaryCentralizerProjection A).range.Normal ∧
      (ordinaryCentralizerProjection A).range.index ≤ 2 ∧
      ((IsSquare lambda.val ∧ SplitMatrixStructure n A lambda) ∨
        ∃ hns : ¬ IsSquare lambda.val, QuadraticMatrixStructure n A lambda hsq hns) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinvolution
  refine ⟨lambda, hsq, ordinaryCentralizerProjection_range_normal A,
    ordinaryCentralizerProjection_range_index_le_two A hinvolution, ?_⟩
  by_cases hs : IsSquare lambda.val
  · exact Or.inl ⟨hs, square_projective_centralizer_structure n hn A lambda htwo hne hsq hs⟩
  · exact Or.inr ⟨hs, nonsquare_projective_centralizer_structure n hn A lambda hsq hs⟩

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
