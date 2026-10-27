module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV46
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest5
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenOA
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2SpinPerfect
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2TorusMain

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge8

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest12 : Prop :=
  SeitzRest5.TwE6ThreeOpenDiagEven ∧ QuasiHigh6.SeitzCoverCubeRest5 ∧ ChevQ.SeitzExcOpenResidual13 ∧
    ChevQ.SeitzE6ThreeConn2

theorem seitzLowRest11_of_rest12 (h : SeitzLowRest12) : SeitzRest5.SeitzLowRest11 :=
  ⟨h.1, h.2.1, h.2.2.1, ChevQ.E6Three.e6NotAll24Census_of_OA ChevQ.E6Three.e6Cen_OA, ChevQ.E6Three.twE6ConnGen_of_d5 h.2.2.2.1,
    ChevQ.E6Three.twE6EightGen, ChevQ.E6Three.d4t2ModelGen_of_parts
      (ChevQ.E6Three.d4t2TorusPart_of_spinPerfect ChevQ.E6Three.d4t2_fixedSpinPerfect) h.2.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge8

end
