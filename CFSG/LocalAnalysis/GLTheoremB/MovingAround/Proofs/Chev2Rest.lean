module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256m2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Chev2Rest

set_option linter.unusedSectionVars false


theorem input25_6A5Rest5_of_rest6 (h : Inputs256m.Chev2GF4Rest ∧ Inputs256d.NoA5On fun d =>
    Inputs256c.defField d.1 = 2 ∧ ∃ q, d.1 = TauCeti.LieTypeIndex.F4 q ∨ d.1 =
    TauCeti.LieTypeIndex.E6 q ∨ d.1 = TauCeti.LieTypeIndex.twistedE6 q ∨ d.1 =
    TauCeti.LieTypeIndex.E7 q ∨ d.1 = TauCeti.LieTypeIndex.E8 q) : Inputs256h.Input25_6A5Rest5 :=
  ⟨Inputs256m.chev2GF4_of_rest h.1, h.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Chev2Rest

end
