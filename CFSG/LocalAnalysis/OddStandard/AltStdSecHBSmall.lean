module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecHBPartsTwo
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupTri
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuterHN
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEvenCenter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveM12NotTop
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseI
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenSmall
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThree
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenFive
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbFinal
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupMain

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG.ComponentClassification CFSG.ComponentClassification.RestrictedStd.Spor


theorem altStdCyclicBalancedFalse_of_small (hIS : AltStdBalancedOrder2InnerSmall)
    (hS2 : ShapeTwoSmall) : AltStdCyclicBalancedFalse :=
  have hHN : HNLocalComponentsInput := hnLocalComponentsInput_holds
  have hFour : FourExactOuterInput :=
    fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB CatLeafProof.monsterInnerInput
  have hlookup : AltComponentLookup :=
    altComponentLookup_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
      CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
      co1LocalComponentsInput_holds hHN hFour lyOuterTrivialInput
      Sporadic.FischerOddCore.fi22OuterComponentsInput_holds CatLeafProof.monsterInnerInput
      CatLeafProof.monsterLocalComponentsInput
  have htri : ExactShapeTrichotomy := exactShapeTrichotomy_of_lookup hlookup hHN
    RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds
  altStdCyclicBalancedFalse_of_parts_shapeTwo hlookup hHN hFour htri hIS hS2
    (RankTwoAlt.rankTwoAlternatingStandard_of_open
        (RankTwoAltFive.altFiveCaseI_of
            (RankTwoAlt.altGenerationFive_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA))
        (RankTwoAltFive.asc310EpsOne_of Asc76X.goldschmidtTheoremA) RankTwoAltFive.asc310IIb
        RankTwoAlt.altFiveM12NotTop_of RankTwoAlt.altEvenCenterSmall RankTwoAlt.altThreeCover
        (RankTwoAlt.altGenerationSmall_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA)
        RankTwoAlt.altRootFusion
        (RankTwoAlt.altTypeTwoFusion_of_rootFusion RankTwoAlt.altRootFusion)
        (RankTwoAlt.altTypeTwoCentralizer Asc76X.goldschmidtTheoremA))

theorem altStdCyclicBalancedFalse_of_small_eleven (hIS : AltStdBalancedOrder2InnerSmall)
    (hS11 : ShapeTwoSmallEleven) (h47 : ShapeTwoCentDoubleAt 12) : AltStdCyclicBalancedFalse :=
  altStdCyclicBalancedFalse_of_small hIS
    (shapeTwoSmall_of_eleven (exactShapeTrichotomy_of_lookup
      (altComponentLookup_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
        CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
        co1LocalComponentsInput_holds hnLocalComponentsInput_holds
        (fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB CatLeafProof.monsterInnerInput)
        lyOuterTrivialInput Sporadic.FischerOddCore.fi22OuterComponentsInput_holds
        CatLeafProof.monsterInnerInput CatLeafProof.monsterLocalComponentsInput)
      hnLocalComponentsInput_holds RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds)
      h47 hS11)

end CFSG.OddStandard.AltStdSec
