module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV44
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge5

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge6

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest9 : Prop :=
  QuasiHigh5E6Cover.TwE6ThreeOpenPlanes ∧ QuasiHigh6.SeitzCoverCubeRest5 ∧ ChevQ.SeitzExcOpenResidual12 ∧
    ChevQ.SeitzE6ThreeCensusTw

theorem seitzLowRest8_of_rest9 (h : SeitzLowRest9) : SeitzYS09Bridge5.SeitzLowRest8 :=
  ⟨h.1, h.2.1, ⟨⟨⟨ChevQ.e7NegCLineRest_holds, h.2.2.1.1.1⟩, ChevQ.threeNonToralCubeRest_F4_holds, h.2.2.1.1.2⟩,
    h.2.2.1.2⟩, h.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge6

end
