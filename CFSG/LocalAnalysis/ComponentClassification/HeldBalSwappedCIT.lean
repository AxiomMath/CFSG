module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalSwapped
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURWire
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFHolds
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13HResiduesB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafHeMainFi24
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REvenOut
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSuz
public import CFSG.Holt.H78.Bridge
public import CFSG.Holt.H78.Theorem1
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNHoltSimple
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHeNDiag
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKDUniversal
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMNMaxTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RMain

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem heldKSwapped_of_cit
    (hCI : GSLit.ClassicalInvolutionInput) (hb : Sol76.Lemma315bInputFor Sol76T13.simpleAmbient) :
    HeldKSwapped := by
  have hS := RankThree.PartOne.SPOR.schreierFor_catalog
  have hGA : TBLit.GriessMultipliersAllModels := TBLit.griessMultipliersAllModels_holds
  have h13 := Sol76T13.solomonThm13Simple_of_schreier hS hb
  have hGLS : CatLeaf.GLS3OddLieAutComponentsInput := gls3OddLieAutComponentsInput_holds
  have hHN : HeldNotProperFixedInput :=
    CatLeaf.heldNotProperFixedInput_of_inputs' hGLS CatLeafProof.lieOrderFormulasInput
      CatLeafProof.evenLieOuterTwoComponentsInput_holds CatLeafProof.monsterInnerInput
      CatLeafProof.monsterLocalComponentsInput KProperRelativeB.sporadicOddCoreFree_M
  have hMax : MaximalTwoComponentInputHe :=
    Sol76.maximalTwoComponentSimple_held hCI hGA h13 hS hHN
  have hU := FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
  have hheld := KProperRelativeB.heldInput
  have hD : L34RankTwoCentralFixedInput :=
    l34RankTwoCentralFixedInput_of_inputs hGA EvenSporadicStandard.centralTwoBound hGLS
      evenLieExcOuterL34Input_holds suzDoubleCoverL34Input_holds
  have hDC : L34ProperFixedCenterTrivial :=
    l34ProperFixedCenterTrivial_of_inputs hGA EvenSporadicStandard.centralTwoBound hGLS
      evenLieExcOuterL34Input_holds suzDoubleCoverL34Input_holds
  have hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple :=
    CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1
  have hSN : HeldSingleNormalStep :=
    HeSN.heldSingleNormalStep_of_holtSimple hMax hS hHN heldSylowElementarySixtyFour
      heldOuterInvolutionRank
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
      heldFourGroupGeneration hHS
  exact heldKSwapped_of_centralStep (heldKDiagonalCentralStep_of_component
    (heldKDiagonalComponentStep_of_rest hD
      (heldKDiagonalComponentRestStep_of_frontier hS hU hheld hD hDC l34ProperFixedSimpleRank_holds
        hMax hHN hSN (heldKDiagonalPumpUpDiagonalResidue_of_involutionFact hS hU hheld
            L34Facts.l34InvolutionCentralizerFact hDC))))

end CFSG.ComponentClassification.GrSLit
