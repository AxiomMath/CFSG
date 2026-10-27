module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem input19_1_3_holds : LocalBalance.Lemma59Ns.Input19_1_3 := by
  intro G _ _ _ _ _ p hp B hB k hk D hD b hbB _ L hL hbal
  exact commutator_le_of_isCompLocallyBalanced hp hB hk hD hbB hL hbal

end CFSG.HardMathSupport.Solomon.Coordinator
