module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV39
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzExcOpenResidual8 : Prop :=
  SeitzExcOpenRest6.SeitzThreeResidual6 ∧ KSE8Five.E8TwoFiveNonToral

theorem seitzExcOpenResidual7_of_residual8 (hres : SeitzExcOpenResidual8) : SeitzExcOpenResidual7 :=
  ⟨hres.1, KSE8Five.e8OneFiveNonToralGriess_holds, hres.2⟩

theorem i271ChevQ_of_inputs_v40 (hres : SeitzExcOpenResidual8) (hE6 : SeitzE6ThreeTwo) : I271ChevQ :=
  i271ChevQ_of_inputs_v39 (seitzExcOpenResidual7_of_residual8 hres) hE6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
