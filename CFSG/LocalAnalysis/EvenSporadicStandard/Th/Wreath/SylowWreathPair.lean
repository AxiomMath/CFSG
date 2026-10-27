module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.Z4Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathTwoElement
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathSylowOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathCase
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.F4Case
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SL7Reduce2

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.false_of_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (F : SylowFacts L S B Aa) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) : False := by
  obtain ⟨Q, T, g, w, hQ, hT, hq4, hsq, hgT, hgQ, hgM, hgw, hwH, hτw, hβ, hΦ, hw0, hw1, hcase⟩ :=
    H.exists_wreath_or_F4 W W2 F hD h4 hb
  rcases hcase with hww | hw2
  · have hp := H.exists_mem_wreathP₁_phiQ_eq W W2 F hD h4 hb hwH hww hτw hw0 hw1 hQ hq4 hsq hβ hΦ
      hgQ hgw hgM
    exact H.false_of_wreath_case W W2 hD h4 hb hwH hww hτw hQ hq4 hsq hΦ hgQ hgw hgM
      (H.exists_le_wreathP₁_card_eq W W2 hD h4 hb hwH hww hτw hw0 hQ hq4 hsq hΦ hgQ hgw hgM hp)
  · exact H.false_of_F4_case W W2 F hD h4 hb hQ hT hq4 hsq hgT hgQ hgM hgw hwH hτw hβ hΦ hw2

theorem thSylowWreathPair : ThSylowWreathPair := by
  intro G _ _ L R t S A B Aa D z b H W W2 F hD h4 hb _ _ _ _ _ _ _ _
  exact (H.false_of_D W W2 F hD h4 hb).elim

end CFSG.EvenSporadicStandard.ThStd
