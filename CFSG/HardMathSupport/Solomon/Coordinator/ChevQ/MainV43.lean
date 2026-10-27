module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV42
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8b

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzThreeResidual9 : Prop :=
  (E7NegCLineRest ∧ E8NegCLineRest) ∧
    (E6ThreeInner.E6InnerCubeGenAt 2 ∧ SeitzExcOpenRest4.SeitzGoodInnerExcThreeTwE6 ∧
      SeitzExcOpenRest5.E7NonToralTwoRest ∧ SeitzExcOpenRest4.ThreeNonToralCubeRest .E8 TauCeti.LieTypeIndex.E8)

@[expose] def SeitzExcOpenResidual11 : Prop :=
  SeitzThreeResidual9 ∧ KSE8Five.E8TwoFiveNonToral

theorem seitzExcOpenResidual10_of_residual11 (hres : SeitzExcOpenResidual11) : SeitzExcOpenResidual10 :=
  ⟨⟨hres.1.1, threeNonToralCubeRest_F4_holds, hres.1.2⟩, hres.2⟩

theorem i271ChevQ_of_inputs_v43 (hres : SeitzExcOpenResidual11) (hE6 : SeitzE6ThreeCensusTw) : I271ChevQ :=
  i271ChevQ_of_inputs_v42 (seitzExcOpenResidual10_of_residual11 hres) hE6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
