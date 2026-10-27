module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILb
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EForms
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Walter.ReeOrder.JT.Defs
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {k : Type} [Field k]

@[expose] def mU1 : Matrix (Fin 4) (Fin 4) k :=
  !![1, 1, 2, 0; 0, 1, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1]

@[expose] def mUw (δ : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, -δ, 0, -2 * δ; 0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 0, 1]

@[expose] def mL1 : Matrix (Fin 4) (Fin 4) k :=
  !![1, 0, 0, 0; 1, 1, 2, 0; 1, 0, 1, 0; 0, 0, 0, 1]

theorem mU1_mulVec (x : Fin 4 → k) :
    (mU1 : Matrix (Fin 4) (Fin 4) k) *ᵥ x = ![x 0 + x 1 + 2 * x 2, x 1, x 2 + x 1, x 3] := by
  funext i
  fin_cases i
  all_goals simp [mU1, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  all_goals ring

theorem mUw_mulVec (δ : k) (x : Fin 4 → k) :
    mUw δ *ᵥ x = ![x 0 - δ * x 1 - 2 * δ * x 3, x 1, x 2, x 3 + x 1] := by
  funext i
  fin_cases i
  all_goals simp [mUw, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  all_goals ring

theorem mL1_mulVec (x : Fin 4 → k) :
    (mL1 : Matrix (Fin 4) (Fin 4) k) *ᵥ x = ![x 0, x 1 + x 0 + 2 * x 2, x 2 + x 0, x 3] := by
  funext i
  fin_cases i
  all_goals simp [mL1, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  all_goals ring

local macro "mnorm" : tactic =>
  `(tactic| (
    simp only [mU1, mUw, mL1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, zero_mul, mul_zero]
    ring1))

theorem schur_matrix {δ : k} (h2 : (2 : k) ≠ 0) {M : Matrix (Fin 4) (Fin 4) k}
    (hU1 : M * mU1 = mU1 * M) (hUw : M * mUw δ = mUw δ * M) (hL1 : M * mL1 = mL1 * M) :
    M = M 0 0 • (1 : Matrix (Fin 4) (Fin 4) k) := by
  have E1 := fun i j => congrFun (congrFun hU1 i) j
  have Ew := fun i j => congrFun (congrFun hUw i) j
  have El := fun i j => congrFun (congrFun hL1 i) j
  have m10 : M 1 0 = 0 := by linear_combination (norm := mnorm) -(E1 2 0)
  have m20 : M 2 0 = 0 := by
    have : (2 : k) * M 2 0 = 0 := by linear_combination (norm := mnorm) -(E1 0 0) - m10
    exact (mul_eq_zero.1 this).resolve_left h2
  have m30 : M 3 0 = 0 := by
    have : (2 : k) * M 3 0 = 0 := by linear_combination (norm := mnorm) E1 3 2
    exact (mul_eq_zero.1 this).resolve_left h2
  have m12 : M 1 2 = 0 := by linear_combination (norm := mnorm) E1 1 1 - m10
  have m32 : M 3 2 = 0 := by linear_combination (norm := mnorm) E1 3 1 - m30
  have m22 : M 2 2 = M 1 1 := by linear_combination (norm := mnorm) E1 2 1 - m20
  have m13 : M 1 3 = 0 := by linear_combination (norm := mnorm) -(E1 2 3)
  have m23 : M 2 3 = 0 := by
    have : (2 : k) * M 2 3 = 0 := by linear_combination (norm := mnorm) -(E1 0 3) - m13
    exact (mul_eq_zero.1 this).resolve_left h2
  have m33 : M 3 3 = M 1 1 := by linear_combination (norm := mnorm) Ew 3 1 + δ * m30
  have m01 : M 0 1 = 0 := by linear_combination (norm := mnorm) -(El 2 1)
  have m21 : M 2 1 = 0 := by
    have : (2 : k) * M 2 1 = 0 := by linear_combination (norm := mnorm) -(El 1 1) - m01
    exact (mul_eq_zero.1 this).resolve_left h2
  have m02 : M 0 2 = 0 := by linear_combination (norm := mnorm) El 0 0 - m01
  have m31 : M 3 1 = 0 := by linear_combination (norm := mnorm) El 3 0 - m32
  have m03 : M 0 3 = 0 := by linear_combination (norm := mnorm) -(El 1 3) - 2 * m23
  have m11 : M 1 1 = M 0 0 := by linear_combination (norm := mnorm) El 1 0 - m12 + 2 * m20
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m10, m20, m30, m12, m32, m13, m23, m01, m21, m02, m31, m03, m22, m33, m11]

end OIL

end CFSG.ComponentClassification.CatFactsL4U4
