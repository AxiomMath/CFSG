module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Cover

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem stepL2_of
    (hE1 : CrossE1) : StepL2 := by
  intro p Γ _ _ V _ _ _ ρ K a hf _ r hr hr2 hrp hL
  obtain ⟨hp3, F₀, _, _, e0, h5, h2⟩ := stepL2_core hE1 hf hr hr2 hrp hL
  exact ⟨hp3, L2Cover.hasSL2Model_five_of_even_center hf.quasi h5 e0 h2⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
