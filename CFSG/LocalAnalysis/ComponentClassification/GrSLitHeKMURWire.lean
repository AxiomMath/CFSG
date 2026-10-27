module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURPump
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDNMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixHeFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGoldschmidt
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitASHe

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG CFSG.LocalAnalysis.ComponentInitial

theorem heldKDiagonalComponentRestStep_of_frontier (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hD : L34RankTwoCentralFixedInput) (hDC : L34ProperFixedCenterTrivial)
    (hH : L34ProperFixedSimpleRank) (hMax : MaximalTwoComponentInputHe)
    (hHN : HeldNotProperFixedInput) (hSN : HeldSingleNormalStep)
    (hKMd : HeldKDiagonalPumpUpDiagonalResidue) : HeldKDiagonalComponentRestStep :=
  heldKDiagonalComponentRestStep_of_pumpUp' hS hUO hheld hD hDC hH
    (heldWGroupStep_of_inputs
      (heldSingleComponentStep_of_normal hSN hMax hS hHN heldSylowElementarySixtyFour
        heldOuterInvolutionRank
        Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
        goldschmidtStronglyClosedInput_holds)
      solomonCommutingCoreInput goldschmidtStronglyClosedInput_holds heldSylowElementarySixtyFour
      heldSylowCenterTwo heldOuterInvolutionRank heldFourGroupGeneration)
    (heldStandardStep_of_inputs
      (heldOddCoreStep_of_central (heldUCentralStep_of_inputs hS hUO hheld hD
        (heldUDiagonalStep_of_meet hS hUO hheld (heldUDiagonalMeetStep_of_inputs hS hUO hheld)))
        Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate hMax hS hHN
        heldSylowElementarySixtyFour)
      hMax hS hHN heldSylowElementarySixtyFour)
    aschbacherSeitzHeldInput_holds hKMd

end CFSG.ComponentClassification.GrSLit
