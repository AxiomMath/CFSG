module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableFam
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem k32ExclPSL42_proved : K32ExclPSL42 := by
  intro K _ _ hq h hK
  exfalso
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff K).mp
    (Or.inl ⟨by decide, h⟩)
  exact hK (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))

end CFSG.QuasithinUnique.DoubleA3
