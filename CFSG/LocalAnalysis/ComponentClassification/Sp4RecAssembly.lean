module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecMain
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecLinearHigh
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecUnitaryHigh
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSympMain
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGU

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def LinearFourExclusion : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (_ : Config H) (p f : ℕ), p.Prime → p ≠ 2 →
    StatedClassicalModel ↥(generalizedFitting H) .PSL 4 p f → False

@[expose] def UnitaryFourExclusion : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (_ : Config H) (p f : ℕ), p.Prime → p ≠ 2 →
    StatedClassicalModel ↥(generalizedFitting H) .PSU 4 p f → False

theorem linearExclusion_of_four (h4 : LinearFourExclusion) : LinearExclusion := by
  intro H _ _ c n p f hp hp2 hG
  have hn : 2 ≤ n := hG.1.2.2.1
  rcases (by omega : n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with rfl | rfl | rfl | hn5
  · exact c.false_of_psl_two hG
  · exact c.false_of_psl_three hp2 hG
  · exact h4 H c p f hp hp2 hG
  · exact c.false_of_linear_high hp hp2 hn5 hG

theorem unitaryExclusion_of_four (h4 : UnitaryFourExclusion) : UnitaryExclusion := by
  intro H _ _ c n p f hp hp2 hG
  have hn : 3 ≤ n := hG.1.2.2.1
  rcases (by omega : n = 3 ∨ n = 4 ∨ 5 ≤ n) with rfl | rfl | hn5
  · exact c.false_of_psu_three hp2 hG
  · exact h4 H c p f hp hp2 hG
  · exact c.false_of_unitary_high hp hp2 hn5 hG

theorem symplecticExclusion : SymplecticExclusion :=
  fun _ _ _ c _ _ _ _ hp2 hn hG => c.false_of_psp_high hp2 hn hG

theorem cfSp4RecognitionCI_of_four (hL : LinearFourExclusion) (hU : UnitaryFourExclusion)
    (hO : OrthogonalExclusion) : GSThmB.CFSp4RecognitionCI :=
  cfSp4RecognitionCI_of_classical (linearExclusion_of_four hL) (unitaryExclusion_of_four hU)
    symplecticExclusion hO

end CFSG.ComponentClassification.Sp4Rec
