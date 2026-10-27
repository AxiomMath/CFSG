module

public import CFSG.CGT.T75H.L2Case
public import CFSG.CGT.T75H.Rank2Stmt
public import CFSG.CGT.T75H.Rank1
public import CFSG.CGT.T75H.Setup

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75

theorem step69_of_noGlauberman (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) (h1 : Sec4NoA) (h63 : Sec63) (h57 : Step57) (hR : Step69Rank2) :
    Step69 := by
  intro G _ T T₁ hy h4
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hc := sec6Ctx_of_card_four h214 hInv hIso hy h4
  have h48 : IsWC (barSub T (normIn T₁ T)) := sec48_of_noA h1 G T T₁ hy hc.hS hc.hI
  obtain ⟨ℓ, a, b, y, D⟩ := exists_d8Data hc
  obtain ⟨S, hS1, hS2, hS3, hS4⟩ := exists_sylow_sStar h1 h63 hc h48
  have hS : SylowData T T₁ S := ⟨hS1, hS2, hS3, hS4⟩
  by_cases hrank : ∀ α ∈ Cbar T T₁ S, ∀ β ∈ Cbar T T₁ S, α * α = 1 → β * β = 1 →
      α * β = β * α → α = 1 ∨ β = 1 ∨ α = β
  · exact listGroup_of_Cbar_bot hy.nonab hc D hS
      (Cbar_eq_bot_of_rank_one hy.nonab (h57 G T T₁ hy) hy.pair.conj D hS hrank)
  · push Not at hrank
    obtain ⟨α, hα, β, hβ, hα2, hβ2, hαβ, hα1, hβ1, hne⟩ := hrank
    exact (hR G T T₁ hy h4 S hS α hα β hβ hα1 hβ1 hne hα2 hβ2 hαβ).elim

end CFSG.CGT.T75H
