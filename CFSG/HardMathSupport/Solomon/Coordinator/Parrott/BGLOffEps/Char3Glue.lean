module

public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

theorem bglFieldGenerationWithXOffEps_of_halves (h3 : BGLOffEpsCharThree) (h8 : BGLOffEpsU38) :
    BGLFieldGenerationWithXOffEps := by
  intro K _ _ hK hT hnot f x hf hf1 hf3 hx hx1 hx3 hfx
  rcases hT with ⟨F, hF, hFfin, ⟨e⟩⟩ | ⟨F, hF, hFfin, q, hcard, ⟨e⟩⟩
  · by_cases h0 : Nat.card F % 3 = 0
    · exact h3 K hK (Or.inl ⟨F, hF, hFfin, h0, ⟨e⟩⟩) f x hf hf1 hf3 hx hx1 hx3 hfx
    · exact absurd (Or.inl ⟨F, hF, hFfin, h0, ⟨e⟩⟩) hnot
  · by_cases h0 : q % 3 = 0
    · exact h3 K hK (Or.inr ⟨F, hF, hFfin, q, hcard, h0, ⟨e⟩⟩) f x hf hf1 hf3 hx hx1 hx3 hfx
    · by_cases hq8 : q = 8
      · subst hq8
        exact h8 K hK ⟨F, hF, hFfin, hcard, ⟨e⟩⟩ f x hf hf1 hf3 hx hx1 hx3 hfx
      · exact absurd (Or.inr ⟨F, hF, hFfin, q, hcard, h0, hq8, ⟨e⟩⟩) hnot

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps
