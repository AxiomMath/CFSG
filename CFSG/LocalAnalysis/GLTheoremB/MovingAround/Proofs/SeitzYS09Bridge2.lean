module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV39
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge2

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest5 : Prop :=
  QuasiHigh5.SeitzCoverFamExcRest2Rest ∧ QuasiHigh4.SeitzCoverCubeRest4 ∧ ChevQ.SeitzExcOpenResidual7 ∧
    ChevQ.SeitzE6ThreeTwo

theorem seitzLowRest4_of_rest5 (h : SeitzLowRest5) : SeitzYS09Bridge.SeitzLowRest4 :=
  ⟨h.1, h.2.1, h.2.2.1, ChevQ.E6Three.e6ThreeCompGen_holds, h.2.2.2.1, ChevQ.E6Three.e6BadCube_of_monomial,
    ChevQ.E6Three.twE6ThreeCompGen_holds, h.2.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge2

end
