module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest9
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311n2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest11

set_option linter.unusedSectionVars false


@[expose] def SeitzThm4Rest12 : Prop :=
  Inputs2311m.D4PlanesRest2 ∧ Inputs2311n.OddCpfInnerExc3

theorem seitzThm4Rest11_of_rest12 (h : SeitzThm4Rest12) : SeitzRest9.SeitzThm4Rest11 :=
  ⟨h.1, Inputs2311n.oddCpfInnerExc2_of_rest3 h.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest11

end
