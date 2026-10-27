module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCoverShape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverSpor
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicMultD1

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.KFactProofs.ThreeCover CFSG.RankThree.PerfectCover
  CFSG.RankThree.PartTwo.Sec4.Census

theorem kFactThreeCoverInvolve_of_multD1
    (hD : SporadicMultipliersD1) : KFactThreeCoverInvolve := by
  intro K _ _ hq hZne hZ hrk B L _ hL f hf
  have hcyc : ∀ {t : TauCeti.SporadicName}, t ∈ sporadicNineList →
      (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic t).Group) →
        IsCyclic (Subgroup.center K) := fun ht e =>
    isCyclic_center_of_dvd hZ hZne
      ((hD.card_center_dvd_three_of_mem (isQuasisimple_of_open hq) hZ ht e).trans (by norm_num))
  refine ⟨fun d hd => ?_, isEmpty_alternating_nine hq hZ hZne, fun s hs => ⟨fun e => ?_⟩⟩
  · rcases hd with ⟨n, hn⟩ | hd
    · exact isEmpty_linTwo_three hq hZ hZne hn
    · exact isEmpty_spFour_three hZ hL B f hf hd
  · rcases hs with ⟨-, hs⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · exact false_J3 hZ hL B f hf e
      · exact false_McL hq hZ hZne (hcyc (by decide) e) hrk e
      · exact false_Suz hZ hZne (hcyc (by decide) e) hrk e
      · exact false_ON hL B f hf e
      · exact false_of_not_dvd_multiplier hq hZ hZne e (hD.three _ (by decide))
      · exact false_of_not_dvd_multiplier hq hZ hZne e (hD.three _ (by decide))
      · exact false_of_not_dvd_multiplier hq hZ hZne e (hD.three _ (by decide))
      · exact false_Fi22 hZ hZne (hcyc (by decide) e) hrk e
      · exact false_of_not_dvd_multiplier hq hZ hZne e (hD.three _ (by decide))
      · exact false_Fi24 hZ hZne (hcyc (by decide) e) hrk e
      · exact false_of_not_dvd_multiplier hq hZ hZne e (hD.three _ (by decide))
      · exact false_of_not_dvd_multiplier hq hZ hZne e (hD.three _ (by decide))
      · exact false_of_not_dvd_multiplier hq hZ hZne e (hD.three _ (by decide))
      · exact false_of_not_dvd_multiplier hq hZ hZne e (hD.three _ (by decide))
      · exact false_of_not_dvd_multiplier hq hZ hZne e (hD.three _ (by decide))
      · exact false_M22 hL B f hf e
    all_goals omega

end CFSG.AGLEmbedding
