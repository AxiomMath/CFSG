module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCQAss
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSteps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Rank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2SetB

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem fzc_sy2_of {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hr : Nat.card (twoCore t) = 2) (hV : FzSylow (l41V S t x₁ x₂))
    (ht : t ∈ fzP t x₁ x₂ rho) : False := by
  have hs := fzc_sy2_str h.ctx hq hr
  have hQ3 : S4A.RankLE (fzQ t x₁ x₂ rho) 3 := fzc_sy2_rank hs ht
  have hQV : fzQ t x₁ x₂ rho ≤ l41V S t x₁ x₂ := by
    rw [hq.Q_eq]
    exact hq.R_le_V
  have hrel : (fzQ t x₁ x₂ rho).relIndex (l41V S t x₁ x₂) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := fzQ t x₁ x₂ rho) (K := l41V S t x₁ x₂)
    rw [inf_eq_left.mpr hQV, hs.card_Q, hq.card_V, hq.card_W, hr] at h1
    omega
  have hV4 : S4A.RankLE (l41V S t x₁ x₂) 4 := S4A.RankLE.of_relIndex_two hQV hrel hQ3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine h.ass (S4A.sectionalTwoRankLE_of_sylow_rank (hV.1.toSylow hV.2) ?_)
  intro X hX
  exact hV4 X (by simpa using hX)

theorem fzc_sy2 :
    FzCSy2 :=
  fun _ _ _ _ _ _ _ _ _ _ h hr hV ht => fzc_sy2_of h (fzc_qfacts_of_steps (fzc_steps h)) hr hV ht

end CFSG.OddStandard.SmallF3.FritzII
