module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddProj
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionNonsquareComponents

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Open CFSG.Open.StatedAPI

theorem hasCompOrSolv_centralizer_GL {K : Type} [Field K] [Finite K] (htwo : (2 : K) ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda) :
    HasCompOrSolv (Subgroup.centralizer ({A} : Set (Matrix.GeneralLinearGroup (Fin n) K))) := by
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, -, hr, hs, -, e, -⟩ :=
      CatalogueBProjectiveInvolution.square_projective_centralizer_structure n hn A lambda htwo
        hne hsq hsquare
    exact HasCompOrSolv.of_mulEquiv e.symm
      ((hasCompOrSolv_GL _ K hr).prod (hasCompOrSolv_GL _ K hs))
  · let : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    let : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite lambda.val
    have hm := (CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A lambda hsq
      hsquare).2
    exact HasCompOrSolv.of_mulEquiv
      (CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq).symm
      (hasCompOrSolv_GL _ _ hm)

theorem matrixDichotomy_statedSL {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (htwo : (2 : K) ≠ 0) : MatrixDichotomy (StatedSL n K) := by
  rintro ⟨A, hA⟩ ⟨u, hu⟩ hns
  have hne : Matrix.ProjGenLinGroup.mk A ≠ 1 := by
    intro h1
    apply hns
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    exact h1
  have hGL : SolvableOrComponent (Matrix.GeneralLinearGroup (Fin n) K) A :=
    hasCompOrSolv_centralizer_GL htwo hn A u hne hu
  have hnorm : (StatedSL n K).subtype.range.Normal := by
    rw [Subgroup.range_subtype, statedSL_eq_ker_det]
    infer_instance
  have hcomm : commutator (Matrix.GeneralLinearGroup (Fin n) K) ≤ (StatedSL n K).subtype.range := by
    rw [Subgroup.range_subtype, statedSL_eq_ker_det]
    exact Abelianization.commutator_subset_ker _
  exact solvableOrComponent_of_inj (StatedSL n K).subtype Subtype.val_injective hnorm hcomm
    ⟨A, hA⟩ hGL

end CFSG.ComponentClassification.CatFC.DS81
