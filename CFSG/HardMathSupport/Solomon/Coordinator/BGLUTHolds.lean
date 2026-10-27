module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUTMain
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUMain
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLHolds

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem bglFieldPairGenerationU_holds :
    BGLFieldPairGenerationU :=
  bglFieldPairGenerationU_of_core BGL.su3SubfieldJoin_holds

theorem bglFieldPairGeneration_holds :
    BGLFieldPairGeneration :=
  bglFieldPairGeneration_of_U bglFieldPairGenerationU_holds

end CFSG.HardMathSupport.Solomon.Coordinator
