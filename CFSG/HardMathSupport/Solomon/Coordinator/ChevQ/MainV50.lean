module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV49
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeSplitHyper
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5Lang

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzExcOpenResidual16 : Prop :=
  E8NegCLineRest ∧
    (E6ThreeF4Close.F4NonToralNegHyperplane ∧ E6ThreeInner.TwE6CaseIFrameH0 ∧ E6ThreeInner.TwE6CaseIICycNonA2 ∧
      E6ThreeInner.TwE6CaseIIRankTwo ∧ SeitzExcOpenRest5.E7NonToralTwoRest ∧
      SeitzExcOpenRest4.ThreeNonToralCubeRest .E8 TauCeti.LieTypeIndex.E8)

theorem seitzExcOpenResidual15_of_residual16 (h : SeitzExcOpenResidual16) : SeitzExcOpenResidual15 :=
  ⟨h.1, h.2.1, E6ThreeF4Close.f4NonToralSplitHyperplane_holds, h.2.2⟩

theorem i271ChevQ_of_inputs_v50 (hres : SeitzExcOpenResidual16) (hE6 : E6Three.KSGen.D5FixedSpinPerfect) :
    I271ChevQ :=
  i271ChevQ_of_inputs_v49 (seitzExcOpenResidual15_of_residual16 hres) (
      E6Three.KSGen.twE6ConnFixed_40_of E6Three.KSGen.d5TorusLang
          (E6Three.KSGen.d5FixedRational_of_perfect hE6))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
