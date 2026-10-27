module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV47
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge8
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Coset

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge9

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest13 : Prop :=
  SeitzRest5.TwE6ThreeOpenDiagEven ∧ QuasiHigh6.SeitzCoverCubeRest5 ∧ ChevQ.SeitzExcOpenResidual13 ∧
    ChevQ.SeitzE6ThreeConn3

theorem seitzLowRest12_of_rest13 (h : SeitzLowRest13) : SeitzYS09Bridge8.SeitzLowRest12 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ChevQ.E6Three.d4t2CosetPart_of_centralTorus h.2.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge9

end
