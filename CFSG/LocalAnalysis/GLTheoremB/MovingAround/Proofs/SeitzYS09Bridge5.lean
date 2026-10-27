module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV42
public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge4

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge5

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest8 : Prop :=
  QuasiHigh5E6Cover.TwE6ThreeOpenPlanes ∧ QuasiHigh6.SeitzCoverCubeRest5 ∧ ChevQ.SeitzExcOpenResidual10 ∧
    ChevQ.SeitzE6ThreeCensusTw

theorem seitzLowRest7_of_rest8 (h : SeitzLowRest8) : SeitzYS09Bridge4.SeitzLowRest7 :=
  ⟨QuasiHigh5E6Cover.seitzCoverFamExcRest2Rest_of_open h.1, h.2.1,
    ⟨⟨h.2.2.1.1.1, h.2.2.1.1.2.1, ChevQ.E6ThreeInner.seitzGoodInnerExcThreeE6_of_cubes
        (ChevQ.E6ThreeInner.e6InnerCubeGen_of_at ChevQ.E6ThreeInner.e6InnerCubeGenAt_one_holds h.2.2.1.1.2.2.1),
        h.2.2.1.1.2.2.2⟩, h.2.2.1.2⟩,
    ⟨ChevQ.E6Three.e6ThreeNotAll24NFA_of_census h.2.2.2.1, h.2.2.2.2⟩⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge5

end
