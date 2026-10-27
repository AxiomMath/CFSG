module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCore
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLHalves

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem bglFieldGenerationThreeL_holds : BGLFieldGenerationThreeL :=
  bglFieldGenerationThreeL_of_core BGL.sl3SubfieldJoin_holds

theorem bglFieldPairGeneration_of_U (hU : BGLFieldPairGenerationU) : BGLFieldPairGeneration :=
  bglFieldPairGeneration_of_core BGL.sl3SubfieldJoin_holds hU

end CFSG.HardMathSupport.Solomon.Coordinator
