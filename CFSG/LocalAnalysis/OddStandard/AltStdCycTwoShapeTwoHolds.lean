module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExMain
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExElevenMain
public import CFSG.LocalAnalysis.OddStandard.RouteWStdEleven
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoYOne
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSevenWeak

public section

namespace CFSG.OddStandard.AltStdCycTwo

section Large


theorem cycTwoShapeTwoLargeFalse_holds : CycTwoShapeTwoLargeFalse :=
  cycTwoShapeTwoLargeFalse_of_centInf cycTwoCentInfLarge_holds AltStdSec.exactShapeTrichotomy_holds
      (ComponentClassification.RankTwoAlt.rankTwoAlternatingStandard_of_open
          (ComponentClassification.RankTwoAltFive.altFiveCaseI_of
              (ComponentClassification.RankTwoAlt.altGenerationFive_of
                  ComponentClassification.AS76b.asc08Lemma34
                  ComponentClassification.Asc76X.goldschmidtTheoremA))
          (ComponentClassification.RankTwoAltFive.asc310EpsOne_of
              ComponentClassification.Asc76X.goldschmidtTheoremA)
          ComponentClassification.RankTwoAltFive.asc310IIb
          ComponentClassification.RankTwoAlt.altFiveM12NotTop_of
          ComponentClassification.RankTwoAlt.altEvenCenterSmall
          ComponentClassification.RankTwoAlt.altThreeCover
          (ComponentClassification.RankTwoAlt.altGenerationSmall_of
              ComponentClassification.AS76b.asc08Lemma34
              ComponentClassification.Asc76X.goldschmidtTheoremA)
          ComponentClassification.RankTwoAlt.altRootFusion
          (ComponentClassification.RankTwoAlt.altTypeTwoFusion_of_rootFusion
              ComponentClassification.RankTwoAlt.altRootFusion)
          (ComponentClassification.RankTwoAlt.altTypeTwoCentralizer
              ComponentClassification.Asc76X.goldschmidtTheoremA))
      (AltStdSec.altComponentLookup_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
          ComponentClassification.CatLeafProof.lieOrderFormulasInput
          ComponentClassification.CatLeafProof.evenLieOuterTwoComponentsInput_holds
          ComponentClassification.RestrictedStd.Spor.co1LocalComponentsInput_holds
          ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds
          (ComponentClassification.RestrictedStd.Spor.fourExactOuterInput_of_BM
              ComponentClassification.BMCase.inner_of_mulEquiv_pinnedB
              ComponentClassification.CatLeafProof.monsterInnerInput)
          ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput
          Sporadic.FischerOddCore.fi22OuterComponentsInput_holds
          ComponentClassification.CatLeafProof.monsterInnerInput
          ComponentClassification.CatLeafProof.monsterLocalComponentsInput)
      ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds
      RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds
      (ComponentClassification.RestrictedStd.Spor.fourExactOuterInput_of_BM
          ComponentClassification.BMCase.inner_of_mulEquiv_pinnedB
          ComponentClassification.CatLeafProof.monsterInnerInput)

end Large

section CentEleven


theorem cycTwoCentInfEleven_holds : CycTwoCentInfEleven :=
  cycTwoCentInfEleven_of_lookup (AltStdSec.weakA7Lookup_of_inputs
      SeitzReduction.gls3OddLieAutComponentsInput
      ComponentClassification.CatLeafProof.lieOrderFormulasInput
      ComponentClassification.CatLeafProof.evenLieOuterTwoComponentsInput_holds)

end CentEleven

section Eleven


theorem cycTwoShapeTwoElevenFalse_holds : CycTwoShapeTwoElevenFalse :=
  cycTwoShapeTwoElevenFalse_of_centInf cycTwoCentInfEleven_holds
      AltStdSec.exactShapeTrichotomy_holds SeitzReduction.gls3OddLieAutComponentsInput
      ComponentClassification.CatLeafProof.lieOrderFormulasInput
      ComponentClassification.CatLeafProof.evenLieOuterTwoComponentsInput_holds
      (ComponentClassification.RankTwoAlt.rankTwoAlternatingStandard_of_open
          (ComponentClassification.RankTwoAltFive.altFiveCaseI_of
              (ComponentClassification.RankTwoAlt.altGenerationFive_of
                  ComponentClassification.AS76b.asc08Lemma34
                  ComponentClassification.Asc76X.goldschmidtTheoremA))
          (ComponentClassification.RankTwoAltFive.asc310EpsOne_of
              ComponentClassification.Asc76X.goldschmidtTheoremA)
          ComponentClassification.RankTwoAltFive.asc310IIb
          ComponentClassification.RankTwoAlt.altFiveM12NotTop_of
          ComponentClassification.RankTwoAlt.altEvenCenterSmall
          ComponentClassification.RankTwoAlt.altThreeCover
          (ComponentClassification.RankTwoAlt.altGenerationSmall_of
              ComponentClassification.AS76b.asc08Lemma34
              ComponentClassification.Asc76X.goldschmidtTheoremA)
          ComponentClassification.RankTwoAlt.altRootFusion
          (ComponentClassification.RankTwoAlt.altTypeTwoFusion_of_rootFusion
              ComponentClassification.RankTwoAlt.altRootFusion)
          (ComponentClassification.RankTwoAlt.altTypeTwoCentralizer
              ComponentClassification.Asc76X.goldschmidtTheoremA))
      (AltStdSec.altComponentLookup_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
          ComponentClassification.CatLeafProof.lieOrderFormulasInput
          ComponentClassification.CatLeafProof.evenLieOuterTwoComponentsInput_holds
          ComponentClassification.RestrictedStd.Spor.co1LocalComponentsInput_holds
          ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds
          (ComponentClassification.RestrictedStd.Spor.fourExactOuterInput_of_BM
              ComponentClassification.BMCase.inner_of_mulEquiv_pinnedB
              ComponentClassification.CatLeafProof.monsterInnerInput)
          ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput
          Sporadic.FischerOddCore.fi22OuterComponentsInput_holds
          ComponentClassification.CatLeafProof.monsterInnerInput
          ComponentClassification.CatLeafProof.monsterLocalComponentsInput)
      ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds
      RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds
      (ComponentClassification.RestrictedStd.Spor.fourExactOuterInput_of_BM
          ComponentClassification.BMCase.inner_of_mulEquiv_pinnedB
          ComponentClassification.CatLeafProof.monsterInnerInput)

end Eleven

end CFSG.OddStandard.AltStdCycTwo
