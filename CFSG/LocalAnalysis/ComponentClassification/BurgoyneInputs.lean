module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataFamily
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates

public section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

@[expose] def oddExceptionalTags : Finset StatedLieTag :=
  {.G2, .F4, .E6, .E7, .E8, .twistedE6, .trialityD4, .twistedG2}

@[expose] def torusExceptionalTags : Finset StatedLieTag := {.E6, .twistedE6, .E7}

@[expose] def BurgoyneExcOddCoreInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    ∀ (τ : StatedLieTag) (n p f : ℕ), τ ∈ oddExceptionalTags → τ ∉ torusExceptionalTags →
      p ≠ 2 → LieModel (GeneralizedFitting.subgroup X) τ n p f →
    ∀ t : X, orderOf t = 2 → oddCentralizerCore t = ⊥

@[expose] def BurgoynePropAE6E7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsM4 X →
    ∀ (τ : StatedLieTag) (n p f : ℕ), τ ∈ torusExceptionalTags → p ≠ 2 →
      LieModel (GeneralizedFitting.subgroup X) τ n p f →
    ∀ t : X, orderOf t = 2 → ∀ Y : Subgroup X, Y ≠ ⊥ → Y ≤ oddCentralizerCore t →
      PropAConclusion X t Y

@[expose] def BurgoyneD4TrialityConjInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 →
    ∀ t : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)), orderOf t = 2 →
      ∃ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
        α * t * α⁻¹ ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K)

@[expose] def BurgoyneD4TrialityOddCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 →
    ∀ B : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))).range ≤ B →
    ∀ t ∈ B, orderOf t = 2 → t ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) →
      oddCoreIn B t ≤ projectivePointFamilyAut (coordinateQuadPlus 4 K)

end CFSG.ComponentClassification.Burgoyne
