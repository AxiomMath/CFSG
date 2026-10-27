module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSplit
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSCATTwo

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup AltStdBal

theorem altStdCyclicOddTwoFalse_of_parts (hBig : CycTwoBigFalse) (hS3 : CycTwoShapeThreeFalse)
    (hIL : CycTwoInnerLargeFalse) (hIS : CycTwoInnerSmallFalse)
    (hTL : CycTwoShapeTwoLargeFalse) (hT11 : CycTwoShapeTwoElevenFalse)
    (hT9 : CycTwoShapeTwoNineFalse) :
    ComponentClassification.SolAltLit.AltStdCyclicOddTwoFalse := by
  intro G _ _ L hS n hodd hn θ hbal S hcyc
  rcases card_eq_two_or_four_le (even_card_centralizer hS) S with h2 | h4
  · obtain ⟨z, d⟩ := cyc_of_sylow hS S hcyc
    have hQ2 : Nat.card (sylowSub S) = 2 := (card_sylowSub S).trans h2
    have hT : OrderTwo G L (sylowSub S) n θ z := ⟨hS, hodd, hn, hbal, d, hQ2⟩
    obtain ⟨k, hk⟩ := hodd
    by_cases hin : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)
    · rcases le_or_gt n 11 with h11 | h12
      · exact hIS G L _ _ θ z hT h11 hin
      · exact hIL G L _ _ θ z hT (by omega) hin
    · obtain ⟨u, huC, huO, hu⟩ := exists_outer_sq hS θ (by omega) d hQ2 hin
      rcases hu with hu1 | huz
      · rcases (show n = 9 ∨ n = 11 ∨ 13 ≤ n by omega) with h9 | h11 | h13
        · subst h9
          exact hT9 G L _ θ z u hT huC huO hu1
        · subst h11
          exact hT11 G L _ θ z u hT huC huO hu1
        · exact hTL G L _ _ θ z u hT h13 huC huO hu1
      · exact hS3 G L _ _ θ z u hT huC huO huz
  · exact hBig G L hS n hodd hn θ hbal S hcyc h4

theorem cycTwoInnerLargeFalse_of_stages (hF : CycTwoInnerFusionAll) (hM : CycTwoInnerStageM)
    (hT : CycTwoWreathFalse) : CycTwoInnerLargeFalse := by
  intro G _ _ L Q n θ z h hn hin
  obtain ⟨M, hM'⟩ := hM G L Q n θ z h hn hin (hF G L Q n θ z h hn hin)
  exact hT G L Q n θ z h hin M hM'

end CFSG.OddStandard.AltStdCycTwo
