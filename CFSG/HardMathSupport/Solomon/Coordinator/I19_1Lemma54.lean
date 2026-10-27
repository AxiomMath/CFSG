module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem input19_1_2_lemma54_holds : LocalBalance.Lemma54Ns.Input19_1_2 := by
  intro G _ _ _ _ _ p hp D hD hD1 b hb _ _
  exact delta_conclusions hp hD hD1 hb

end CFSG.HardMathSupport.Solomon.Coordinator
