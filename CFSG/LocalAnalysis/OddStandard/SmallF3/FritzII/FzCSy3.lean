module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCQAss
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSteps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem fzc_sy3_of {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hr : Nat.card (twoCore t) = 4) (hV : FzSylow (l41V S t x₁ x₂)) : False := by
  by_cases ht : t ∈ fzP t x₁ x₂ rho
  · exact fzc_sy3_b_of h hq hr hV ht
  · exact fzc_sy3_a_of h hq hr hV ht

theorem fzc_sy3 :
    FzCSy3 :=
  fun _ _ _ _ _ _ _ _ _ _ h hr hV => fzc_sy3_of h (fzc_qfacts_of_steps (fzc_steps h)) hr hV

end CFSG.OddStandard.SmallF3.FritzII
