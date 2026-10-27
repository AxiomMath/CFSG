module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.AsmPump
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.AsmDispatch
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm2Main
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm3Main
public import CFSG.LocalAnalysis.OddStandard.ChildHeHeld

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG.Open CFSG.ComponentClassification CFSG.ComponentClassification.HarrisLit


theorem f3HigherRankFalse_of_inputs (hT1 : Harris82Theorem1KProper) (hID : IdentGenInput)
    (hHB : HardBranchInputBalanced) (hGA : TBLit.GriessMultipliersAllModels)
    (hC2 : POmegaPlusCentreExpTwo) (hC4 : POmegaPlusNotLinUnit) : F3HigherRankFalse := by
  intro G _ _ L hset hF3
  have hstd := hset.std.standard
  haveI : IsSimpleGroup G := hset.std.simple
  obtain ⟨-, hs⟩ := hstd.1
  obtain ⟨t, ht, ht2⟩ := CFSG.OddStandard.exists_involution_of_standard hstd
  obtain ⟨hLt, hLp⟩ := CFSG.OddStandard.isPComponent_two_of_standard hstd ht ht2
    (even_iff_two_dvd.mp (CFSG.OddStandard.even_card_of_standard hstd))
  exact pumpUpFalse hT1 hID (theorem3Full_of hT1 (theorem2ClassB_of hT1 hID)) hHB hset.std.nonab
    hset.std.kProper hset.notCat hset.balanced ht2 hLt hLp
    (hasClassBMember_of_hrF3 hGA hC2 hC4 hF3)

end CFSG.OddStandard.HigherRank.F3
