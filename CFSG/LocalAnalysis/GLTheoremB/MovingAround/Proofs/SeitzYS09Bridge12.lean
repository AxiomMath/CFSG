module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV50
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge11

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge12

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest16 : Prop :=
  CubeCoverE6.CoverE6DiagNotAll24 ∧ CubeCoverE6.CoverTwE6Cubes ∧ ChevQ.SeitzExcOpenResidual16 ∧
    ChevQ.E6Three.KSGen.D5FixedSpinPerfect

theorem seitzLowRest15_of_rest16 (h : SeitzLowRest16) : SeitzYS09Bridge11.SeitzLowRest15 :=
  ⟨h.1, h.2.1, ⟨h.2.2.1.1, h.2.2.1.2.1, ChevQ.E6ThreeF4Close.f4NonToralSplitHyperplane_holds, h.2.2.1.2.2⟩,
    ChevQ.E6Three.KSGen.twE6ConnFixed_40_of ChevQ.E6Three.KSGen.d5TorusLang
        (ChevQ.E6Three.KSGen.d5FixedRational_of_perfect h.2.2.2)⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge12

end
