module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecHBParts
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarFourteen
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoThirteen
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoTwelve

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RestrictedStd.Spor

@[expose] def ShapeTwoSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ) (z u : G),
    Setting G L n → Cyc L Q z → ShapeTwo L Q z u → n ≤ 12 → False

theorem altStdBalancedOrder2OuterSmall_of_shapeTwoSmall
    (htri : ExactShapeTrichotomy) (hR2 : RankTwoAlternatingStandard) (hS2 : ShapeTwoSmall) :
    AltStdBalancedOrder2OuterSmall := by
  intro G _ _ L hS n hn hn13 hθ S hcyc h2 hbal hex
  have h : Setting G L n := ⟨hS, hn, hθ, ⟨S, hcyc⟩, hbal⟩
  refine false_of_outer_of_shapeTwo h S hcyc h2 hex fun Q z u d T => ?_
  rcases Nat.lt_or_ge n 13 with h12 | h13
  · exact hS2 G L Q n z u h d T (by omega)
  · obtain rfl : n = 13 := by omega
    obtain ⟨e⟩ := hθ
    exact false_of_shapeTwo_thirteen htri hR2 h d T e

@[expose] def ShapeTwoSmallEleven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ) (z u : G),
    Setting G L n → Cyc L Q z → ShapeTwo L Q z u → n ≤ 11 → False

theorem shapeTwoSmall_of_eleven
    (htri : ExactShapeTrichotomy) (h47 : ShapeTwoCentDoubleAt 12) (h11 : ShapeTwoSmallEleven) :
    ShapeTwoSmall := by
  intro G _ _ L Q n z u h d T hn
  rcases Nat.lt_or_ge n 12 with h12 | h12
  · exact h11 G L Q n z u h d T (by omega)
  · obtain rfl : n = 12 := by omega
    obtain ⟨e⟩ := h.iso
    exact false_of_shapeTwo_twelve htri h47 h d T e

section Certified


theorem altStdCyclicBalancedFalse_of_parts_rankTwo
    (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (htri : ExactShapeTrichotomy)
    (hIS : AltStdBalancedOrder2InnerSmall) (hOS : AltStdBalancedOrder2OuterSmall)
    (hR2 : RankTwoAlternatingStandard) : AltStdCyclicBalancedFalse :=
  altStdCyclicBalancedFalse_of_parts hlookup hHN hFour htri hIS hOS
    (shapeTwoCaseIIClassification_of_rankTwo' htri hR2)

theorem altStdCyclicBalancedFalse_of_parts_shapeTwo
    (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (htri : ExactShapeTrichotomy)
    (hIS : AltStdBalancedOrder2InnerSmall) (hS2 : ShapeTwoSmall)
    (hR2 : RankTwoAlternatingStandard) : AltStdCyclicBalancedFalse :=
  altStdCyclicBalancedFalse_of_parts_rankTwo hlookup hHN hFour htri hIS
    (altStdBalancedOrder2OuterSmall_of_shapeTwoSmall htri hR2 hS2) hR2

end Certified

end CFSG.OddStandard.AltStdSec
