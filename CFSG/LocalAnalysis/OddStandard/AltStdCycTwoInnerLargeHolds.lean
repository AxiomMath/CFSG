module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageF
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupMain
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuterHN
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageM
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageT
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoMain

public section

namespace CFSG.OddStandard.AltStdCycTwo

open CFSG.ComponentClassification CFSG.ComponentClassification.RestrictedStd.Spor AltStdSec


theorem cycTwoInnerStageM_holds : CycTwoInnerStageM :=
  cycTwoInnerStageM_of_inputs
    (altComponentLookup_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
      CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
      co1LocalComponentsInput_holds hnLocalComponentsInput_holds
      (fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB CatLeafProof.monsterInnerInput)
      lyOuterTrivialInput Sporadic.FischerOddCore.fi22OuterComponentsInput_holds
      CatLeafProof.monsterInnerInput CatLeafProof.monsterLocalComponentsInput)
    hnLocalComponentsInput_holds RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds
    (fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB CatLeafProof.monsterInnerInput)

theorem cycTwoInnerLargeFalse_holds : CycTwoInnerLargeFalse :=
  cycTwoInnerLargeFalse_of_stages (cycTwoInnerFusionAll_of_inputs
      (altComponentLookup_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
          CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
          co1LocalComponentsInput_holds hnLocalComponentsInput_holds
          (fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB CatLeafProof.monsterInnerInput)
          lyOuterTrivialInput Sporadic.FischerOddCore.fi22OuterComponentsInput_holds
          CatLeafProof.monsterInnerInput CatLeafProof.monsterLocalComponentsInput)
      hnLocalComponentsInput_holds RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds
      (fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB CatLeafProof.monsterInnerInput)) cycTwoInnerStageM_holds
    cycTwoWreathFalse_holds

end CFSG.OddStandard.AltStdCycTwo
