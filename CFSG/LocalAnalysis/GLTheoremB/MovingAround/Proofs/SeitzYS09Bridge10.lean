module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV48
public import CFSG.LieType.SeitzGeneration.CubeCoverE6Rest
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge9
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CentralTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge10

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest14 : Prop :=
  SeitzRest5.TwE6ThreeOpenDiagEven ∧ CubeCoverE6.CoverE6DiagNotAll24 ∧ CubeCoverE6.CoverTwE6Cubes ∧
    ChevQ.SeitzExcOpenResidual14 ∧ ChevQ.E6Three.KSGen.TwE6ConnFixed 40

theorem seitzLowRest13_of_rest14 (h : SeitzLowRest14) : SeitzYS09Bridge9.SeitzLowRest13 :=
  ⟨h.1, CubeCoverE6.seitzCoverCubeRest5_of h.2.1 h.2.2.1,
    ⟨h.2.2.2.1.1, ChevQ.E6ThreeF4Close.e6F4CubeD4Two_of_negHyperplane h.2.2.2.1.2.1,
      ChevQ.E6ThreeF4Close.twE6F4CubeD4One_of_splitHyperplane h.2.2.2.1.2.2.1,
      ChevQ.E6ThreeInner.twE6InnerCubeGenAt_two_of_cases h.2.2.2.1.2.2.2.1 h.2.2.2.1.2.2.2.2.1
        h.2.2.2.1.2.2.2.2.2.1,
      h.2.2.2.1.2.2.2.2.2.2.1, h.2.2.2.1.2.2.2.2.2.2.2⟩,
    h.2.2.2.2, ChevQ.E6Three.d4t2CentralTorus_holds⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge10

end
