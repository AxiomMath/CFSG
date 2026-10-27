module

public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.OddStandard.ChildL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34OddLieStd
public import CFSG.LocalAnalysis.OddStandard.L34SeitzSimple
public import CFSG.LocalAnalysis.OddStandard.Seitz77Proved
public import CFSG.LocalAnalysis.OddStandard.L34EvenSylow
public import CFSG.LocalAnalysis.OddStandard.ChengHeldFinalHyp
public import CFSG.LocalAnalysis.OddStandard.ONanEndConsumer
public import CFSG.LocalAnalysis.OddStandard.ONanB2Mirror
public import CFSG.LocalAnalysis.OddStandard.RouteWStdONan
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalStageU
public import CFSG.Goldschmidt.Final
public import CFSG.LocalAnalysis.ComponentClassification.AS81Open
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Open
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuH1Final
public import CFSG.Sporadic.SuzRecog.MixedCell
public import CFSG.Sporadic.SuzRecog.SuzLeaf
public import Certificates.Certificate431004
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Size
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma37
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20

public section

namespace CFSG.ComponentClassification.GSThmB

theorem l34StandardInput_of_ci
    (hCI : GSLit.ClassicalInvolutionInput) : L34StandardInput := by
  have hGH : UFrontier.GH74ModelsInput := Milestones.cl_lit_gh74_sectional_two_rank_four_models
  have hStU : OddStandard.ONanRec.StageU Blueprint.NativeSporadic.ON :=
    GrSLit.ONanBal.stageU_ON_of_thmC (OddStandard.ThmC.thmCFull_of_gh74 hGH)
      CFSG.Goldschmidt.coreStatement
  have hON : GrSLit.ONanSylowInput :=
    OddStandard.ONanRec.onanSylowInput_of_bal
      (OddStandard.ONanRec.sylowBal_ON_of_loc hGH OddStandard.ONanRec.B2.stageB2Loc_holds) hStU
  have hEven : OddStandard.L34CyclicEvenCenter :=
    OddStandard.l34CyclicEvenCenter_of_sylowStep OddStandard.ChengHeld.l34EvenSylowStep_holds hON
  have hOdd : OddStandard.L34CyclicOddCenter :=
    OddStandard.l34CyclicOddCenter_of_seitzSimple
      (OddStandard.Seitz77.seitz77SimpleL34_of_gh74 hGH)
  have hRank : OddStandard.RankTwoL3FourStandard :=
    OddStandard.rankTwoL3FourStandard_of_rankTwoL3EvenStandard
      (AS81.rankTwoL3EvenStandard_of_open (GMS78.rankTwoBenderStandard_of_open GMS78.ruH1Stmt)
        Sporadic.SuzRecog.MixedCell.mixedCellDichotomy)
  exact OddStandard.l34StandardInput_of_childL34
    (OddStandard.childL34_of_cases hRank hCI OddStandard.oddLieNoStandardL34_holds hOdd hEven)

end CFSG.ComponentClassification.GSThmB
