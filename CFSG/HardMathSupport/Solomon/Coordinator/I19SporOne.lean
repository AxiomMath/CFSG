module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporOpen

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator

set_option linter.unusedSectionVars false


theorem sporadicOneParts_of_open
    (hBRc : BThreeFi23.BThreeRc) (hBRd : BThreeFi23.BThreeRd) (hB5A : BFiveNonCentral)
    (hM3K : TwoAPureKlein 3 CFSG.Monster.Generated.Gmat)
    (hM5K : TwoATwoCommuting 5 CFSG.Monster.Generated.Gmat)
    (hM7cl : MonsterSevenClasses CFSG.AGLEmbedding.Norton.MON5_7.dG
      CFSG.AGLEmbedding.Norton.MON5_7.zG) : SporadicOneParts := by
  have hO := sporadicOnePairOPrime_of_open hBRc hBRd hB5A hM3K hM5K hM7cl
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  exact
    { J3_three := sporadicOnePairHolds_J3 (hbr .J3)
      McL_three := sporadicOnePairHolds_McL
      Suz_three := ⟨hO _ _ (by decide), sporadicOuterHolds_Suz_three⟩
      ONan_three := ⟨hO _ _ (by decide), sporadicOuterHolds_ONan_three⟩
      Co3_three := ⟨hO _ _ (by decide), sporadicOuterHolds_Co3 3⟩
      Co2_three := ⟨hO _ _ (by decide), sporadicOuterHolds_Co2 3⟩
      Co1_three := ⟨hO _ _ (by decide), sporadicOuterHolds_Co1 3⟩
      Fi22_three := ⟨hO _ _ (by decide), sporadicOuterHolds_Fi22_three⟩
      Fi23_three := ⟨hO _ _ (by decide), sporadicOuterHolds_Fi23 3⟩
      Fi24Prime_three := ⟨hO _ _ (by decide), sporadicOuterHolds_Fi24_three⟩
      HN_three := sporadicOnePairHolds_HN_three
      Ly_three := ⟨hO _ _ (by decide), sporadicOuterHolds_Ly 3⟩
      Th_three := ⟨hO _ _ (by decide), sporadicOuterHolds_Th 3⟩
      B_three := ⟨hO _ _ (by decide), sporadicOuterHolds_B 3⟩
      M_three := ⟨hO _ _ (by decide), sporadicOuterHolds_M 3⟩
      Co1_five := ⟨hO _ _ (by decide), sporadicOuterHolds_Co1 5⟩
      HN_five := ⟨hO _ _ (by decide), sporadicOuterHolds_HN_five⟩
      Ly_five := ⟨hO _ _ (by decide), sporadicOuterHolds_Ly 5⟩
      B_five := ⟨hO _ _ (by decide), sporadicOuterHolds_B 5⟩
      M_five := ⟨hO _ _ (by decide), sporadicOuterHolds_M 5⟩
      M_seven := ⟨hO _ _ (by decide), sporadicOuterHolds_M 7⟩ }

end CFSG.HardMathSupport.Solomon.Coordinator
