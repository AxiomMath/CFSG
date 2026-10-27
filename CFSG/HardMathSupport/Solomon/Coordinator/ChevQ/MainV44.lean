module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV43
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest9

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzThreeResidual10 : Prop :=
  E8NegCLineRest ∧
    (E6ThreeInner.E6InnerCubeGenAt 2 ∧ SeitzExcOpenRest4.SeitzGoodInnerExcThreeTwE6 ∧
      SeitzExcOpenRest5.E7NonToralTwoRest ∧ SeitzExcOpenRest4.ThreeNonToralCubeRest .E8 TauCeti.LieTypeIndex.E8)

@[expose] def SeitzExcOpenResidual12 : Prop :=
  SeitzThreeResidual10 ∧ KSE8Five.E8TwoFiveNonToral

theorem seitzExcOpenResidual11_of_residual12 (hres : SeitzExcOpenResidual12) : SeitzExcOpenResidual11 :=
  ⟨⟨⟨e7NegCLineRest_holds, hres.1.1⟩, hres.1.2⟩, hres.2⟩

theorem i271ChevQ_of_inputs_v44 (hres : SeitzExcOpenResidual12) (hE6 : SeitzE6ThreeCensusTw) : I271ChevQ :=
  i271ChevQ_of_inputs_v43 (seitzExcOpenResidual11_of_residual12 hres) hE6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
