module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDelta
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem psuModel_holds : PSUModel := by
  intro p f K _ h hq D H hD hcard hH A hα
  exact psuConj_eq_one_of_mem_localDeltaIn h hq hD hcard hH hα

end CFSG.HardMathSupport.Solomon.Coordinator
