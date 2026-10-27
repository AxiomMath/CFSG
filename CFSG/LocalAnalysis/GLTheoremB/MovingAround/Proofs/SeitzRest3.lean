module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest3

@[expose] def SeitzThm4Rest5 :
    Prop :=
  Inputs2311c.UniSeitzPlanes Inputs2311f.OddCpfRest3 ∧ Inputs256e.Input14_2StructThree

set_option linter.unusedSectionVars false


theorem seitzThm4Rest4_of_rest5 (h : SeitzThm4Rest5) : SeitzRest2.SeitzThm4Rest4 :=
  Inputs256j.seitzThm4Rest4_of_uniSeitz h.1 h.2

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest3

end
