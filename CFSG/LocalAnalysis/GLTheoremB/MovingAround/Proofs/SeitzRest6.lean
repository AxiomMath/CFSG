module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest5
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256n2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest6

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzThm4Rest8 : Prop :=
  Inputs2311c.UniSeitzPlanes Inputs2311g.OddCpfRest4

theorem seitzThm4Rest7_of_rest8 (h : SeitzThm4Rest8) : SeitzRest5.SeitzThm4Rest7 :=
  ⟨h, Inputs256n.qGen3ExcInndiagF3_holds, Inputs256n.qGen3TwE6InndiagF3_holds,
    Inputs256n.qGen3TriD4InnerF3_holds⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest6

end
