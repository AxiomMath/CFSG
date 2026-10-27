module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV45
public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6CoverTw
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge6

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge7

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest10 : Prop :=
  QuasiHigh5E6Cover.TwE6ThreeOpenDiag ∧ QuasiHigh6.SeitzCoverCubeRest5 ∧ ChevQ.SeitzExcOpenResidual13 ∧
    ChevQ.SeitzE6ThreeConn

theorem seitzLowRest9_of_rest10 (h : SeitzLowRest10) : SeitzYS09Bridge6.SeitzLowRest9 :=
  ⟨QuasiHigh5E6Cover.twE6ThreeOpenPlanes_of QuasiHigh5E6Cover.twE6ThreeOpenInner_holds h.1, h.2.1,
    ⟨⟨h.2.2.1.1, ChevQ.E6ThreeF4Close.e6InnerCubeGenAt_two_of_d4 ChevQ.threeNonToralCubeRest_F4_holds h.2.2.1.2.1,
        ChevQ.E6ThreeInner.seitzGoodInnerExcThreeTwE6_of_cubes (ChevQ.E6ThreeInner.twE6InnerCubeGen_of_at
          (ChevQ.E6ThreeF4Close.twE6InnerCubeGenAt_one_of_d4 ChevQ.threeNonToralCubeRest_F4_holds h.2.2.1.2.2.1)
          h.2.2.1.2.2.2.1),
        h.2.2.1.2.2.2.2.1, h.2.2.1.2.2.2.2.2⟩,
      ChevQ.KSE8Five.e8TwoFiveNonToral_holds⟩,
    ⟨h.2.2.2.1, ChevQ.E6Three.twE6NotAll24Gen_of_gen h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge7

end
