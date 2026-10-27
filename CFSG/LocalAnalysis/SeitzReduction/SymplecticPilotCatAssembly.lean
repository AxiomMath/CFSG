module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAssemblyStatement
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuterHolds

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput involutionCentralizersComponentFree_of_evenLieType)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

theorem catSp2mEvenInner :
    CatSp2mEvenInner := by
  intro S _ _ hS hna heven σ hσ hin m f D hD _
  have := hS
  exact F4Pilot.false_of_isComponent_fixedSubgroup_inner hna
    (involutionCentralizersComponentFree_of_evenLieType heven) hσ hin hD

section Assembly

theorem sp2mCatalogueClausesAt_of_inputs (hGLS : GLS3OddLieAutComponentsInput) {m : ℕ}
    (hX : Sp2mNotOddLieInput m) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp2mSporadicResidual m) :
    Sp2mCatalogueClausesAt m :=
  ⟨catSp2mAlternating, catSp2mEvenInner, catSp2mEvenOuter_holds m,
    catSp2mOddLie_of_inputs hGLS hX, catSp2mSporadic_of_residual hMinn hMcomp hres, catSp2mCovers⟩

end Assembly

end CFSG.SeitzReduction.SymplecticPilot
