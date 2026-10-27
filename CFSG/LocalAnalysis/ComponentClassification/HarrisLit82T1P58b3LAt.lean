module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LConfig
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

theorem harris82Lemma58bThreeRowAt_of_two_le (h51E4 : Harris82Lemma51E4) {τ : StatedLieTag}
    {n f : ℕ} (hf : 2 ≤ f) : P58b3.Harris82Lemma58bThreeRowAt τ n f := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ _ hz₁L _ he₁ hKc hO₁ _ _ hz₂K hz₂Z hm
  have := P58b3L.field_eq_one h51E4 hz₁ hz₂ hL₁ hz₁L he₁ hKc hO₁ hz₂K hz₂Z hm
  omega

end CFSG.ComponentClassification.HarrisLit.T1
