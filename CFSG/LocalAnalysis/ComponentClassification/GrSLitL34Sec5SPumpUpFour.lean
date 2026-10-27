module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SPumpUpFive
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdONanHolds
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardExclusion
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdResidualFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REvenOut
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSuz
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFHolds
public import CFSG.LocalAnalysis.ComponentClassification.Foote1978.SolomonThm13
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMNMaxTwo
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMNSFL
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldProved

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

theorem l34SuzONanFieldPumpUpExclusion_of_three_residuals
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hSSuz : L34SuzStandardExclusion) (hSField : L34FieldStandardExclusion)
    (hCField : L34FieldCoreStepMirror) :
    L34SuzONanFieldPumpUpExclusion :=
  l34SuzONanFieldPumpUpExclusion_of_five_residuals hCI h13 hSSuz
    (l34ONanStandardExclusion_holds hCI) hSField (l34SuzCoreStepMirror_holds hCI h13) hCField

theorem l34SuzONanFieldPumpUpExclusion_holds :
    L34SuzONanFieldPumpUpExclusion :=
  l34SuzONanFieldPumpUpExclusion_of_three_residuals FooteLit.classicalInvolutionInput_holds
    FooteLit.solomonThm13Simple_holds
    (l34SuzStandardExclusion_of_four_residuals FooteLit.classicalInvolutionInput_holds
      FooteLit.solomonThm13Simple_holds FooteLit.classicalInvolutionInput_holds
      l34FieldStandardExclusion_holds)
    l34FieldStandardExclusion_holds
    (l34FieldCoreStepMirror_of_mirror_ascent RankThree.PartOne.SPOR.schreierFor_catalog
      FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds FooteLit.classicalInvolutionInput_holds
      FooteLit.solomonThm13Simple_holds)

theorem l34Cor217ComponentStep_holds :
    L34Cor217ComponentStep :=
  l34Cor217ComponentStep_of_suzONanField RankThree.PartOne.SPOR.schreierFor_catalog
    (l34ProperFixedCenterTrivial_of_inputs
        CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
        CFSG.EvenSporadicStandard.centralTwoBound gls3OddLieAutComponentsInput_holds
        evenLieExcOuterL34Input_holds suzDoubleCoverL34Input_holds) l34ProperFixedSimpleRank_holds
    l34SuzONanFieldPumpUpExclusion_holds

end CFSG.ComponentClassification.GrSLit.L34Sec5S

namespace CFSG.ComponentClassification.GrSLit

theorem maximalTwoComponentInput_holds :
    MaximalTwoComponentInput := by
  intro G _ _ _ hsF hnF hoF hK J hJ h2 hSp htype t ht hJt
  rcases htype with ⟨hL34, hbase⟩ | hHe
  · exact Sol76.maximalTwoComponentSimple_l34 FooteLit.classicalInvolutionInput_holds
      TBLit.griessMultipliersAllModels_holds FooteLit.solomonThm13Simple_holds
      RankThree.PartOne.SPOR.schreierFor_catalog (l34ProperFixedCenterTrivial_of_inputs
          CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
          CFSG.EvenSporadicStandard.centralTwoBound gls3OddLieAutComponentsInput_holds
          evenLieExcOuterL34Input_holds suzDoubleCoverL34Input_holds)
      l34ProperFixedSimpleRank_holds
      (L34Sec5S.l34CyclicPumpUpExclusion_of_catalog L34Sec5S.l34CyclicProperFixedCatalog_holds
        L34Sec5S.l34SuzONanFieldPumpUpExclusion_holds)
      hbase hsF hnF hoF hJ h2 hL34 ht hJt
  · exact Sol76.maximalTwoComponentSimple_held FooteLit.classicalInvolutionInput_holds
      TBLit.griessMultipliersAllModels_holds FooteLit.solomonThm13Simple_holds
      RankThree.PartOne.SPOR.schreierFor_catalog heldNotProperFixedInput_holds G hsF hnF hoF hK
      J hJ h2 hSp hHe t ht hJt

theorem solomonFixedLayerStep_holds :
    SolomonFixedLayerStep := by
  intro G _ _ _ hsF hnF hoF hK a J ha hJa hJp _ hL34 hbase g _ hbN hbO
  exact SFL.solomonFixedLayer_at_of_solomonMaximal FooteLit.classicalInvolutionInput_holds
    TBLit.griessMultipliersAllModels_holds FooteLit.solomonThm13Simple_holds hsF hnF hoF hK ha
    hJa hJp hL34
    (Foote5.SolMax.isSolomonMaximal_of_gsMirrorMaximal hsF hnF ha ⟨hJa, hJp⟩
      (L34Sec5S.gsMirrorMaximal_of_cyclicExclusion RankThree.PartOne.SPOR.schreierFor_catalog
        (l34ProperFixedCenterTrivial_of_inputs
            CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
            CFSG.EvenSporadicStandard.centralTwoBound gls3OddLieAutComponentsInput_holds
            evenLieExcOuterL34Input_holds suzDoubleCoverL34Input_holds) l34ProperFixedSimpleRank_holds
        (L34Sec5S.l34CyclicPumpUpExclusion_of_catalog L34Sec5S.l34CyclicProperFixedCatalog_holds
          L34Sec5S.l34SuzONanFieldPumpUpExclusion_holds) hbase hL34))
    g hbN hbO

end CFSG.ComponentClassification.GrSLit
