module

public import CFSG.LieType.SeitzGeneration.QuasiHigh6Rest
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest6 : Prop :=
  QuasiHigh5.SeitzCoverFamExcRest2Rest ∧ QuasiHigh6.SeitzCoverCubeRest5 ∧ ChevQ.SeitzExcOpenResidual7 ∧
    ChevQ.SeitzE6ThreeTwo

theorem seitzLowRest5_of_rest6 (h : SeitzLowRest6) : SeitzYS09Bridge2.SeitzLowRest5 :=
  ⟨h.1, QuasiHigh6.seitzCoverCubeRest4_of_rest5 h.2.1, h.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge3

end
