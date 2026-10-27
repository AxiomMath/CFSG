module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge14
public import CFSG.LieType.SeitzGeneration.CubeCoverTwE6Rest
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Residual16Holds
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocks
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Core

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge15

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest19 : Prop :=
  CubeCoverE6.CoverTwE6NegDatum ∧ CubeCoverE6.CoverTwE6DiagNotAll24

theorem seitzLowRest18_of_rest19 (h : SeitzLowRest19) : SeitzYS09Bridge14.SeitzLowRest18 :=
  ⟨CubeCoverE6.coverTwE6Cubes_of h.1 h.2,
    ChevQ.seitzExcOpenResidual16_of_e8 ChevQ.E8NonToral.e8ThreeKilledPlaneBlocks_holds
      ChevQ.E8NonToral.e8NonToralD4Core_holds⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge15

end
