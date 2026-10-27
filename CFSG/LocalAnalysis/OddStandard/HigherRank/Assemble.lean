module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.Trichotomy
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Balanced
public import CFSG.LocalAnalysis.OddStandard.HigherRank.CatalogCase

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG.Yardstones.M0362f3a873a3

section


theorem catalogCaseHolds_of_pumpLeaf
    (hP1 : ComponentClassification.GS82PumpInputs.ChevOddPumpLeaf) : CatalogCaseHolds :=
  fun _ _ _ _ hS hcat hlie hF3 hL2 hA6 => oddLieType_of_catalog hP1 hS hcat hlie hF3 hL2 hA6

end

theorem assemble (hC : CatalogCaseHolds) (hA : ClassicalFalse) (hF3 : F3HigherRankFalse)
    (hG23 : G23StandardFalse) : OddLieThm187bResidualHigherRank := by
  intro G _ _ L hS hU hlie hF3' hL2 h5 h6 hhsf hcase S hcyc
  by_cases hcat : CFSG.Blueprint.Catalog G
  · exact Or.inr (Or.inl (hC G L hS hcat hlie hF3' hL2 h6))
  · exfalso
    haveI : IsSimpleGroup G := hS.simple
    have hset : HRSetting G L :=
      ⟨hS, hcat, fun _ hz => oddCore_eq_bot_of_not_catalog hU hcat hz, hlie, hF3', hL2, h5, h6,
        hhsf, hcase, ⟨S, hcyc⟩⟩
    rcases hr_trichotomy hlie hF3' hL2 with h | h | h
    · exact hA G L hset h
    · exact hF3 G L hset h
    · exact hG23 G L hset h

end CFSG.OddStandard.HigherRank
