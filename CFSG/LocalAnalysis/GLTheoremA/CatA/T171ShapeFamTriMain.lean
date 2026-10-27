module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriExit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10


theorem innerCompNonShape_triality_charTwo_of (hC : TriCompClassical) (hA : TriCompAction) :
    InnerCompNonShape fun i => KD264Lie.isTrialityIdx i ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hS hcat hshape hin
  exact innDiagOn_of_triModel hC hA hS (triModel_of_setup hS hshape hin hcat)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
