module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV40
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest7

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzThreeResidual7 : Prop :=
  (E7NegCLineRest ∧ E8NegCLineRest) ∧
    (SeitzExcOpenRest4.ThreeNonToralCubeRest .F4 TauCeti.LieTypeIndex.F4 ∧
      SeitzExcOpenRest4.SeitzGoodInnerExcThreeE6 ∧ SeitzExcOpenRest4.SeitzGoodInnerExcThreeTwE6 ∧
        SeitzExcOpenRest5.E7NonToralTwoRest ∧ SeitzExcOpenRest4.ThreeNonToralCubeRest .E8 TauCeti.LieTypeIndex.E8)

@[expose] def SeitzExcOpenResidual9 : Prop :=
  SeitzThreeResidual7 ∧ KSE8Five.E8TwoFiveNonToral

theorem seitzExcOpenResidual8_of_residual9 (hres : SeitzExcOpenResidual9) : SeitzExcOpenResidual8 :=
  ⟨seitzThreeResidual6_of_toral hres.1.1 hres.1.2, hres.2⟩

theorem i271ChevQ_of_inputs_v41 (hres : SeitzExcOpenResidual9) (hE6 : SeitzE6ThreeTwo) : I271ChevQ :=
  i271ChevQ_of_inputs_v40 (seitzExcOpenResidual8_of_residual9 hres) hE6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
