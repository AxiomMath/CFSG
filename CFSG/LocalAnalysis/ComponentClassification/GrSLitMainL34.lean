module

public import CFSG.Holt.H78.Bridge
public import CFSG.Holt.H78.Theorem1
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafHeMainFi24
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMNMaxTwo
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKDUniversal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURWire
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNHoltSimple
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFHolds
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REvenOut
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSuz
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHeNDiag
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13HResiduesB
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.KProperRelativeB

open CFSG.Assembly CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Certified

theorem heldKDiagonalCentralStep_noL34
    (hCI : GSLit.ClassicalInvolutionInput)
    (hb : Sol76.Lemma315bInputFor Sol76T13.simpleAmbient) :
    GrSLit.HeldKDiagonalCentralStep := by
  have hS := RankThree.PartOne.SPOR.schreierFor_catalog
  have hGA : TBLit.GriessMultipliersAllModels := TBLit.griessMultipliersAllModels_holds
  have hGLS : CatLeaf.GLS3OddLieAutComponentsInput := GrSLit.gls3OddLieAutComponentsInput_holds
  have h13 : Sol76T13.SolomonThm13Simple := Sol76T13.solomonThm13Simple_of_schreier hS hb
  have hHN : GrSLit.HeldNotProperFixedInput :=
    CatLeaf.heldNotProperFixedInput_of_inputs' hGLS CatLeafProof.lieOrderFormulasInput
      CatLeafProof.evenLieOuterTwoComponentsInput_holds CatLeafProof.monsterInnerInput
      CatLeafProof.monsterLocalComponentsInput KProperRelativeB.sporadicOddCoreFree_M
  have hMaxHe : GrSLit.MaximalTwoComponentInputHe :=
    Sol76.maximalTwoComponentSimple_held hCI hGA h13 hS hHN
  have hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple :=
    CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1
  have hU := FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
  have hheld := KProperRelativeB.heldInput
  have hDC : GrSLit.L34ProperFixedCenterTrivial :=
    GrSLit.l34ProperFixedCenterTrivial_of_inputs hGA EvenSporadicStandard.centralTwoBound hGLS
      GrSLit.evenLieExcOuterL34Input_holds GrSLit.suzDoubleCoverL34Input_holds
  have hD : GrSLit.L34RankTwoCentralFixedInput :=
    GrSLit.l34RankTwoCentralFixedInput_of_inputs hGA EvenSporadicStandard.centralTwoBound hGLS
      GrSLit.evenLieExcOuterL34Input_holds GrSLit.suzDoubleCoverL34Input_holds
  have hSN : GrSLit.HeldSingleNormalStep :=
    GrSLit.HeSN.heldSingleNormalStep_of_holtSimple hMaxHe hS hHN
      GrSLit.heldSylowElementarySixtyFour GrSLit.heldOuterInvolutionRank
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
      GrSLit.heldFourGroupGeneration hHS
  exact GrSLit.heldKDiagonalCentralStep_of_component
    (GrSLit.heldKDiagonalComponentStep_of_rest hD
      (GrSLit.heldKDiagonalComponentRestStep_of_frontier hS hU hheld hD hDC
        GrSLit.l34ProperFixedSimpleRank_holds hMaxHe hHN hSN
        (GrSLit.heldKDiagonalPumpUpDiagonalResidue_of_involutionFact hS hU hheld
            GrSLit.L34Facts.l34InvolutionCentralizerFact hDC)))

theorem heldCase_noL34
    (hCI : GSLit.ClassicalInvolutionInput)
    (hb : Sol76.Lemma315bInputFor Sol76T13.simpleAmbient) :
    GrSLit.HeldCase := by
  have hS := RankThree.PartOne.SPOR.schreierFor_catalog
  have hGA : TBLit.GriessMultipliersAllModels := TBLit.griessMultipliersAllModels_holds
  have hGLS : CatLeaf.GLS3OddLieAutComponentsInput := GrSLit.gls3OddLieAutComponentsInput_holds
  have h13 : Sol76T13.SolomonThm13Simple := Sol76T13.solomonThm13Simple_of_schreier hS hb
  have hHN : GrSLit.HeldNotProperFixedInput :=
    CatLeaf.heldNotProperFixedInput_of_inputs' hGLS CatLeafProof.lieOrderFormulasInput
      CatLeafProof.evenLieOuterTwoComponentsInput_holds CatLeafProof.monsterInnerInput
      CatLeafProof.monsterLocalComponentsInput KProperRelativeB.sporadicOddCoreFree_M
  have hMaxHe : GrSLit.MaximalTwoComponentInputHe :=
    Sol76.maximalTwoComponentSimple_held hCI hGA h13 hS hHN
  have hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple :=
    CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1
  have hU := FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
  have hheld := KProperRelativeB.heldInput
  have hD : GrSLit.L34RankTwoCentralFixedInput :=
    GrSLit.l34RankTwoCentralFixedInput_of_inputs hGA EvenSporadicStandard.centralTwoBound hGLS
      GrSLit.evenLieExcOuterL34Input_holds GrSLit.suzDoubleCoverL34Input_holds
  have hSN : GrSLit.HeldSingleNormalStep :=
    GrSLit.HeSN.heldSingleNormalStep_of_holtSimple hMaxHe hS hHN
      GrSLit.heldSylowElementarySixtyFour GrSLit.heldOuterInvolutionRank
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
      GrSLit.heldFourGroupGeneration hHS
  have hKDC : GrSLit.HeldKDiagonalCentralStep := heldKDiagonalCentralStep_noL34 hCI hb
  have hSC : GrSLit.HeldSingleComponentStep :=
    GrSLit.heldSingleComponentStep_of_normal hSN hMaxHe hS hHN
      GrSLit.heldSylowElementarySixtyFour GrSLit.heldOuterInvolutionRank
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
      GrSLit.goldschmidtStronglyClosedInput_holds
  have hOdd : GrSLit.HeldOddCoreStep :=
    GrSLit.heldOddCoreStep_of_central (GrSLit.heldUCentralStep_of_inputs hS hU hheld hD
      (GrSLit.heldUDiagonalStep_of_meet hS hU hheld
        (GrSLit.heldUDiagonalMeetStep_of_inputs hS hU hheld)))
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate hMaxHe hS hHN
      GrSLit.heldSylowElementarySixtyFour
  have hEnd : GrSLit.HeldEndStep :=
    GrSLit.heldEndStep_of_frontiers (GrSLit.heldKNormalStep_of_diagonalStep hS hU hheld hD
      (GrSLit.heldKDiagonalStep_of_central hS hU hheld hKDC)
      (GrSLit.heldKNormalFromComponent_of_inputs GrSLit.heldKInvariantComponentStep))
  exact GrSLit.heldCase_of_steps
    (GrSLit.heldWGroupStep_of_inputs hSC GrSLit.solomonCommutingCoreInput
      GrSLit.goldschmidtStronglyClosedInput_holds GrSLit.heldSylowElementarySixtyFour
      GrSLit.heldSylowCenterTwo GrSLit.heldOuterInvolutionRank GrSLit.heldFourGroupGeneration)
    (GrSLit.heldStandardStep_of_inputs hOdd hMaxHe hS hHN GrSLit.heldSylowElementarySixtyFour)
    GrSLit.aschbacherSeitzHeldInput_holds hEnd

end Certified

end CFSG.ComponentClassification.KProperRelativeB
