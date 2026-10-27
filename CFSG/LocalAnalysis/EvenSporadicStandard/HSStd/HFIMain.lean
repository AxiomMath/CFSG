module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Five
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIL2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIL34
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFILie
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIM12
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFISeven

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem eq_bot_of_normal_odd_of_zStar_eq_bot {K : Type} [Group K] (hZ : fusionZStar K = ⊥)
    (N : Subgroup K) (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have h1 : N ≤ fusionOddCore K :=
    le_sSup (show N ∈ {N : Subgroup K | N.Normal ∧ Odd (Nat.card N)} from ⟨hN, hodd⟩)
  have h2 : fusionOddCore K ≤ fusionZStar K := by
    intro x hx
    show QuotientGroup.mk' (fusionOddCore K) x ∈ Subgroup.center (K ⧸ fusionOddCore K)
    rw [show QuotientGroup.mk' (fusionOddCore K) x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  exact le_bot_iff.1 (h1.trans (h2.trans hZ.le))

theorem haradaFourInspection_proved :
    HaradaFourInspection := by
  intro K _ _ hZ hcase a b ha hb hab hcomm hga hgb hgab
  have hZ' : ∀ N : Subgroup K, N.Normal → Odd (Nat.card N) → N = ⊥ := fun N hN hodd =>
    eq_bot_of_normal_odd_of_zStar_eq_bot hZ N hN hodd
  rcases hcase with hE | hL25 | hL35 | hU35 | h7 | hM | hL34
  · exact (HFI.false_of_good_triple_A5A5 ha hb hab hcomm hga hgb hgab hE).elim
  · exact (HFI.false_of_good_triple_psl_two_twentyfive hZ' ha hb hab hcomm hga hgb hgab hL25).elim
  · exact (HFI.false_of_good_triple_psl_three_five hZ' ha hb hab hcomm hga hgb hgab hL35).elim
  · exact (HFI.false_of_good_triple_psu_three_five hZ' ha hb hab hcomm hga hgb hgab hU35).elim
  · obtain ⟨e7⟩ := h7
    exact (HFI.false_of_good_triple_perm_seven e7 ha hb hab hcomm hga hgb hgab).elim
  · exact ⟨hM, HFI.exists_fusing_of_good_triple_m12 hM ha hb hab hcomm hga hgb hgab⟩
  · exact (HFI.false_of_good_triple_l34 hZ' ha hb hab hcomm hga hgb hgab hL34).elim

end CFSG.EvenSporadicStandard.HSStd
