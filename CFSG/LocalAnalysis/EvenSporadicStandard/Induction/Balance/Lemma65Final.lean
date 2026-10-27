module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.M24Cat
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic

theorem m23Facts_of_certs :
    M23Facts :=
  ⟨CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2, CFSG.EvenSmallLie.CatalogOrders.card_M23⟩

theorem m24Recognition_of_certs :
    M24Recognition := by
  intro G _ hK K L hKtop hLK _ hs hord
  exact CFSG.EvenSporadicStandard.TwoFi22.DS81.isSporadic_M24_of_kProper_section hK hKtop hLK hs
    hord

theorem m24Multiplier_of_certs :
    M24Multiplier := by
  intro X _ hX
  obtain ⟨e⟩ := hX
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_of_mulEquiv
    e]
  exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M24.trans (by decide)

theorem sol78Lemma65KP_of_uniq
    (hU : Sol78Lemma65Uniq) : Sol78Lemma65KP :=
  sol78Lemma65KP_of_inputs hU m23Facts_of_certs m24Recognition_of_certs m24Multiplier_of_certs

end CFSG.EvenSporadicStandard.Induction.Balance
