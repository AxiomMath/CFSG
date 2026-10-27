module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest8
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311m

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest9

set_option linter.unusedSectionVars false


@[expose] def SeitzThm4Rest11 : Prop :=
  Inputs2311m.D4PlanesRest2 ∧ Inputs2311j.OddCpfInnerExc2

theorem seitzThm4Rest10_of_rest11 (h : SeitzThm4Rest11) : SeitzRest8.SeitzThm4Rest10 :=
  ⟨Inputs2311m.d4PlanesRest_of_rest2 h.1, h.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest9

end
