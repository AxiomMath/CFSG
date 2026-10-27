module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256f2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest2

@[expose] def SeitzThm4Rest4 :
    Prop :=
  Inputs2311c.UniSeitzPlanes Inputs2311f.OddCpfRest3 ∧ Inputs256f.QGenExcInndiag ∧ Inputs256f.QGenTwE6Inndiag ∧
    Inputs256f.QGenTriD4Rest ∧ Inputs256e.Input14_2StructThree

set_option linter.unusedSectionVars false


theorem seitzThm4Rest3_of_rest4 (h : SeitzThm4Rest4) : SeitzRest.SeitzThm4Rest3 :=
  ⟨h.1, Inputs256f.qGenSympOrth_holds, Inputs256f.qGenExc_of_inndiag h.2.1 h.2.2.1 h.2.2.2.1, h.2.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest2

end
