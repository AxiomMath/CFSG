module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest7
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311j2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest8

set_option linter.unusedSectionVars false


@[expose] def SeitzThm4Rest10 : Prop :=
  Inputs2311k.D4PlanesRest ∧ Inputs2311j.OddCpfInnerExc2

theorem seitzThm4Rest9_of_rest10 (h : SeitzThm4Rest10) : SeitzRest7.SeitzThm4Rest9 :=
  ⟨h.1, Inputs2311j.oddCpfInnerExc_of_rest h.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest8

end
