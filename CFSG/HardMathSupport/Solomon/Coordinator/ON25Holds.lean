module

public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Top
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Main
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultSporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator


theorem onGeneration_holds : ONGeneration :=
  onGeneration_of_mult (CFSG.EvenSporadicStandard.Induction.onMultThree_of_sporadicMultipliers
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)

theorem lemma55_input23_26_of_BGL (hA : BGLFieldPairGeneration) :
    LocalBalance.Lemma55Ns.Input23_26 :=
  lemma55_input23_26_of_residuals hA onGeneration_holds

end CFSG.HardMathSupport.Solomon.Coordinator
