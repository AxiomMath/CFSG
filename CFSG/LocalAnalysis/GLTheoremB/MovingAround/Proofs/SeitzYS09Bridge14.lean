module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge13
import CFSG.LieType.SeitzGeneration.CubeCoverE6Bad

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge14

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest18 : Prop :=
  CubeCoverE6.CoverTwE6Cubes ∧ ChevQ.SeitzExcOpenResidual16

theorem seitzLowRest17_of_rest18 (h : SeitzLowRest18) : SeitzYS09Bridge13.SeitzLowRest17 :=
  ⟨CubeCoverE6.coverE6DiagNotAll24_holds, h.1, h.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge14

end
