module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem input19_3_1_holds : LocalBalance.Input19_3_1 := by
  intro G _ _ _ _ _ p hp B hB k hk D hD b hbB _ hweak
  exact delta2At_conclusions hp hB hk hD hbB hweak

end CFSG.HardMathSupport.Solomon.Coordinator
