module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinMain
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge12

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge13

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest17 : Prop :=
  CubeCoverE6.CoverE6DiagNotAll24 ∧ CubeCoverE6.CoverTwE6Cubes ∧ ChevQ.SeitzExcOpenResidual16

theorem seitzLowRest16_of_rest17 (h : SeitzLowRest17) : SeitzYS09Bridge12.SeitzLowRest16 :=
  ⟨h.1, h.2.1, h.2.2, ChevQ.E6Three.KSGen.d5_fixedSpinPerfect⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge13

end
