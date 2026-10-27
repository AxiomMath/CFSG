module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV36
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzExcOpenResidual6 : Prop :=
  SeitzExcOpenRest6.SeitzThreeResidual6 ∧ SeitzExcOpenRest4.E8OneFiveCubeRest4 ∧
    SeitzExcOpenRest3.E8TwoFiveCubeRest ∧ SeitzExcOpenRest3.E8FourFiveCubeRest

theorem i271ChevQ_of_inputs_v37 (hres : SeitzExcOpenResidual6) (hE6 : SeitzE6ThreeRest) : I271ChevQ :=
  i271ChevQ_of_inputs_v36 ⟨SeitzExcOpenRest6.seitzThreeResidual5_of_residual6 hres.1, hres.2⟩ hE6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
