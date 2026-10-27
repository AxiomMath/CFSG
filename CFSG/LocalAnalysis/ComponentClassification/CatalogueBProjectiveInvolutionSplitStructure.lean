module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

open CatalogueBProjectiveCoordinates

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem projective_nontrivial_operator_nonscalar [Nonempty ι]
    (A : Matrix.GeneralLinearGroup ι K) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1) :
    ∀ c : K, splitMatrixOperator A ≠ c • (1 : Module.End K (ι → K)) := by
  intro c hscalar
  have hc : c ≠ 0 := by
    intro hc
    have hzero : matrixActionEquiv A (fun _ => 1) = matrixActionEquiv A 0 := by
      change splitMatrixOperator A (fun _ => 1) = splitMatrixOperator A 0
      rw [hscalar, hc]
      simp
    have hv := (matrixActionEquiv A).injective hzero
    exact one_ne_zero (congrFun hv (Classical.choice inferInstance))
  have hA : A = Matrix.GeneralLinearGroup.scalar ι (Units.mk0 c hc) := by
    apply matrixActionEquiv.injective
    apply LinearEquiv.toLinearMap_injective
    rw [matrixActionEquiv_scalar]
    exact hscalar
  exact hne (hA ▸ Matrix.ProjGenLinGroup.mk_scalar (Units.mk0 c hc))

theorem exists_unit_square_root (lambda : Kˣ) (hsquare : IsSquare lambda.val) :
    ∃ b : Kˣ, b ^ 2 = lambda := by
  obtain ⟨b, hb⟩ := (isSquare_iff_exists_sq lambda.val).mp hsquare
  have hnonzero : b ≠ 0 := by
    intro hzero
    exact lambda.ne_zero (by simp [hzero] at hb)
  refine ⟨Units.mk0 b hnonzero, Units.ext ?_⟩
  exact hb.symm

theorem square_projective_centralizer_structure (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (htwo : (2 : K) ≠ 0) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda)
    (hsquare : IsSquare lambda.val) :
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
            q ⟨ordinaryCentralizerProjection A B, ⟨B, rfl⟩⟩ = QuotientGroup.mk (e B)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨b, hb⟩ := exists_unit_square_root lambda hsquare
  have hsqb : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) (b ^ 2) := by
    rw [hb]
    exact hsq
  obtain ⟨hr, hs⟩ := splitMatrixDimension_pos A b htwo hsqb
    (projective_nontrivial_operator_nonscalar A hne)
  refine ⟨b, hb, hr, hs, ?_, matrixCentralizerSplitEquiv A b htwo hsqb,
    projectiveSplitQuotientEquiv A b htwo hsqb,
    matrixCentralizerSplitEquiv_scalar A b htwo hsqb,
    matrixCentralizerSplitEquiv_apply A b htwo hsqb,
    projectiveSplitQuotientEquiv_projection A b htwo hsqb⟩
  simpa only [Fintype.card_fin] using splitMatrixDimension_sum A b htwo hsqb

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
