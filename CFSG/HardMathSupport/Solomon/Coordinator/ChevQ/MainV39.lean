module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV38
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompGen

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzE6ThreeTwo : Prop :=
  E6Three.E6ThreeNotAll24NFA ∧ E6Three.TwE6NotAll24Gen

theorem seitzE6ThreeFive_of_two (h : SeitzE6ThreeTwo) : SeitzE6ThreeFive :=
  ⟨E6Three.e6ThreeCompGen_holds, h.1, E6Three.e6BadCube_of_monomial, E6Three.twE6ThreeCompGen_holds, h.2⟩

theorem i271ChevQ_of_inputs_v39 (hres : SeitzExcOpenResidual7) (hE6 : SeitzE6ThreeTwo) : I271ChevQ :=
  i271ChevQ_of_inputs_v38 hres (seitzE6ThreeFive_of_two hE6)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
