module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MainDvd47
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma57
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Finkelstein55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Eight55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MonsterLocalProof

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.EvenSporadicStandard.TwoFi22 CFSG.LargeExtraspecial.Bridge
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977


theorem twoBGivesM_of_local_direct (hT : Timmesfeld78Co1Dvd47) (hLoc : TwoBLocalData)
    (h54 : DS81Lemma54) (h55 : DS81Lemma55) : TwoBGivesM := by
  intro G _ _ L hstd h2 hQ
  have := hstd.simple
  obtain ⟨t, ht2, htZ⟩ := exists_map_center_eq_zpowers h2
  have hS : Setting G L t := ⟨hstd, h2, hQ, htZ⟩
  have htmem : t ∈ (center L).map L.subtype := htZ ▸ mem_zpowers t
  obtain ⟨t', ht'c, rfl⟩ := htmem
  have ht'2 : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht2
  have hcov : IsTwoBCover L := IsTwoBCover.of_stdHyp hstd h2 hQ
  obtain ⟨z', hz', hz0'⟩ := hLoc L hcov t' ht'c ht'2
  have hc : CentralPair G L (t' : G) (z' : G) := ⟨t'.2, z'.2, hz', hz0'⟩
  have hc54 := h54 G L _ _ hS hc
  have h55' := h55 G L _ _ hS hc hc54
  have hPR := ds81Lemma57Direct G L _ _ hS hc hc54 h55'
  have h47 : 47 ∣ Nat.card G := by
    obtain ⟨e⟩ := hQ
    have h1 : Nat.card (L ⧸ center L) = Nat.card (Carrier .B) := Nat.card_congr e.toEquiv
    have h3 : Nat.card L = Nat.card (L ⧸ center L) * Nat.card (center L) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    have h4 : 47 ∣ Nat.card (Carrier .B) := by
      have : Nat.card (Carrier .B) = CFSG.Open.monsterBabyOrder := card_nativeB
      rw [this]
      norm_num [CFSG.Open.monsterBabyOrder]
    rw [← h1] at h4
    exact h4.trans ((Dvd.intro _ h3.symm).trans (Subgroup.card_subgroup_dvd_card L))
  have hleech := gmsLeechCentralizer_of_timmesfeld_dvd47 hT h47 hc hc54 h55' hPR
  obtain ⟨d₀, hd₀, hrank⟩ := exists_d0
  exact isSporadic_M_of_gmsF1Type hd₀ hrank
    ⟨gmsDoubleF2Centralizer_of_setting hS h55'.centralizer_eq hd₀, hleech⟩

theorem twoBGivesM_of_mainStatement_direct (hM : MainStatement) (h54 : DS81Lemma54)
    (h55 : DS81Lemma55) : TwoBGivesM :=
  twoBGivesM_of_local_direct (timmesfeld78Co1Dvd47_of_mainStatement hM)
    (twoBLocal_of_monster monsterLocal) h54 h55

theorem twoBGivesM_of_hypothesisOne_direct (hM : MainStatement) (h54 : DS81Lemma54)
    (hI : HypothesisOne (Carrier .B)) (h25 : Finkelstein77.Asc76Lemma25)
    (h552 : DS81Lemma55Fusion) : TwoBGivesM :=
  twoBGivesM_of_mainStatement_direct hM h54
    (ds81Lemma55_of_residuals
      (ds81Lemma55CentralizerEq_of_finkelstein hI exists_isElemAbelian_eight_B h25) h552)

end CFSG.EvenSporadicStandard.TwoB
