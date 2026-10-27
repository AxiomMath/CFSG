module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV41
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge3

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge4

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest7 : Prop :=
  QuasiHigh5.SeitzCoverFamExcRest2Rest ∧ QuasiHigh6.SeitzCoverCubeRest5 ∧ ChevQ.SeitzExcOpenResidual9 ∧
    ChevQ.SeitzE6ThreeTwo

theorem seitzLowRest6_of_rest7 (h : SeitzLowRest7) : SeitzYS09Bridge3.SeitzLowRest6 :=
  ⟨h.1, h.2.1, ⟨ChevQ.seitzThreeResidual6_of_toral h.2.2.1.1.1 h.2.2.1.1.2,
    ChevQ.KSE8Five.e8OneFiveNonToralGriess_holds, h.2.2.1.2⟩, h.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge4

end
