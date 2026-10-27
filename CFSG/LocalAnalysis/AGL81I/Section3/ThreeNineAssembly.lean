module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThree
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (ThreeNine)

theorem catalogue24_12Five_of_catalogue (hCat : Catalogue24_12) : Catalogue24_12Five :=
  fun X _ _ K E p hp hp5 hKq hOp hKcat hKn hE hEc hrk hΓ =>
    hCat X K E p hp (by omega) hKq hOp hKcat hKn hE hEc hrk hΓ

theorem threeNine_of_parts (hCat : Catalogue24_12)
    (hSz : ThreeNineFiveSz) (hDef : ThreeNineFiveDef) (hAlt : ThreeNineFiveAlt)
    (hTits : ThreeNineFiveTits) (hExtra : ThreeNineFiveSporExtra) (hFi : ThreeNineFiveFi22)
    (hBig : ThreeNineFiveSporBig)
    (hL34 : ThreeNineThreeL34) (hA6 : ThreeNineThreeA6Hat) (hL28 : ThreeNineThreeL28)
    (hD42 : ThreeNineThreeD42) (hChev : ThreeNineThreeChev) (hAlt3 : ThreeNineThreeAlt)
    (hSp : ThreeNineThreeSp62) (hTits3 : ThreeNineThreeTits) (hSpor : ThreeNineThreeSpor)
    (hCov : ThreeNineThreeCoverRank) (hMcL : ThreeNineThreeMcLRank) : ThreeNine := by
  refine threeNine_of_hyp fun X _ _ K E D X₁ p d h => ?_
  have hp2 := h.prime.two_le
  by_cases hp3 : p = 3
  · subst hp3
    have hΓ := threeNine_not_le_gammaOver K E D X₁ 3 d h.prime h.d_prime h.sylow h.D_ne_bot
      h.lt h.gammaE h.gammaD
    have hrk : CFSG.Open.pRank 3 (K ⊔ E) ≤ 3 :=
      (CFSG.SectionRank.pRank_mono h.prime.one_lt (le_top : K ⊔ E ≤ ⊤)).trans h.rank_le
    exact threeNineThree_of_members hL34 hA6 hL28 hD42 hChev hAlt3 hSp hTits3 hSpor hCov hMcL h
      (hCat X K E 3 h.prime h.ne_two h.quasisimple h.core h.kgroup h.normal h.elem h.card_E hrk hΓ)
  · have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h4 => by
        have := h.prime
        rw [h4] at this
        exact absurd this (by decide)
      have := h.ne_two
      omega
    exact threeNineFive_of_members (catalogue24_12Five_of_catalogue hCat) hSz hDef hAlt hTits
      hExtra hFi hBig h hp5

end CFSG.LocalAnalysis.AGL81I.Section3
