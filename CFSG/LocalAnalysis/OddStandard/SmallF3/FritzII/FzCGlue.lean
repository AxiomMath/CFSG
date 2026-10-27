module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCQAss
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSteps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY6

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

theorem fzc_sy_of
    (h1 : FzCSy1) (h2 : FzCSy2) (h3 : FzCSy3) : FzCSy := by
  intro G _ _ t L S x₁ x₂ lam rho h hV
  rcases (fzc_qfacts_of_steps (fzc_steps h)).card_K with hK | hK
  · by_cases ht : t ∈ fzP t x₁ x₂ rho
    · exact h2 G t L S x₁ x₂ lam rho h hK hV ht
    · exact h1 G t L S x₁ x₂ lam rho h hK hV ht
  · exact h3 G t L S x₁ x₂ lam rho h hK hV

theorem fzc_ns_of (h1 : FzCNS1) (h2 : FzCNS2) : FzCNS := by
  intro G _ _ t L S x₁ x₂ lam rho h hV
  by_cases hV1 : 2 ∣ (l41V1 t x₁ x₂ rho lam).index
  · exact h1 G t L S x₁ x₂ lam rho h hV hV1
  · exact h2 G t L S x₁ x₂ lam rho h hV hV1

theorem fzc_of_split
    (hSy : FzCSy) (hNS : FzCNS) : FzCaseI := by
  intro G _ _ _ t L S x₁ x₂ lam rho hII h0 hPL
  have h : FzCCtx G t L S x₁ x₂ lam rho := ⟨inferInstance, hII, h0, hPL⟩
  by_cases hV : FzSylow (l41V S t x₁ x₂)
  · exact hSy G t L S x₁ x₂ lam rho h hV
  · refine hNS G t L S x₁ x₂ lam rho h ?_
    have hp : IsPGroup 2 (l41V S t x₁ x₂) := (fzc_qfacts_of_steps (fzc_steps h)).V_isFzT2.isPGroup
    by_contra hodd
    exact hV ⟨hp, hodd⟩

end CFSG.OddStandard.SmallF3.FritzII
