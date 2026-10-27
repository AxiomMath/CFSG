module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E7NonToralAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E7KilledPlaneBlocks

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

set_option linter.unusedSectionVars false

section Rest

theorem e7NonToralTwoRest_holds : SeitzExcOpenRest5.E7NonToralTwoRest :=
  e7NonToralTwoRest_of_blocks e7ThreeKilledPlaneBlocks_holds

end Rest

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

end
