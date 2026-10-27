module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem input19_1_2_lemma25_holds : LocalBalance.Lemma25Ns.Input19_1_2 := by
  intro G _ _ _ _ _ p hp k hk D hD hcard b hb _ _
  exact delta_normalizes_and_not_balanced hp hk hD hcard hb

end CFSG.HardMathSupport.Solomon.Coordinator
