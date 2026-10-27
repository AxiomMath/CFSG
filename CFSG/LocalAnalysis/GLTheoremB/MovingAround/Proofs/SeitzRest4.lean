module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256i2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest3

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest4

set_option linter.unusedSectionVars false


@[expose] def SeitzThm4Rest6 : Prop :=
  Inputs2311c.UniSeitzPlanes Inputs2311f.OddCpfRest3 ∧ Inputs256i.QGen3ExcInndiagF3 ∧
    Inputs256i.QGen3TwE6InndiagF3 ∧ Inputs256i.QGen3TriD4InnerF3

theorem seitzThm4Rest5_of_rest6 (h : SeitzThm4Rest6) : SeitzRest3.SeitzThm4Rest5 :=
  ⟨h.1, Inputs256i.input14_2StructThree_of_families h.2.1 h.2.2.1 h.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest4

end
