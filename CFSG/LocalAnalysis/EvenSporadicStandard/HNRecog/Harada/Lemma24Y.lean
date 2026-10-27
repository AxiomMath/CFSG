module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Q
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24QuotTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24QuotNormal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24QuotFP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24QuotI

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.SectionRank

theorem false_of_cfg24 (hGH : GH73.GH73TheoremA64K) {Y : Type} [Group Y] [Finite Y]
    (hK : IsKGroupCat Y) {a t : Y} {τ : Y → Prop} {F P : Subgroup Y}
    (h : Cfg24 Y a t τ F P) : False := by
  haveI : (zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr h.a_central)
  obtain ⟨hFp, hFz, hPF, hPcard, hPA8⟩ := quot_FP_data h
  obtain ⟨M, hMC, hMp, hM⟩ := quot_perfect60 h
  obtain ⟨I, hIcard, hI, hJ⟩ := quot_involutions h
  have hx2 : (QuotientGroup.mk' (zpowers a) t) ^ 2 = 1 := by
    rw [← map_pow, h.t_sq, map_one]
  have hx1 : QuotientGroup.mk' (zpowers a) t ≠ 1 := by
    intro hx
    have ht_z : t ∈ zpowers a :=
      (QuotientGroup.eq_one_iff (N := zpowers a) t).mp
        (by simpa only [QuotientGroup.mk'_apply] using hx)
    have hdvd2 : orderOf t ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h.t_sq
    have hdvd3 : orderOf t ∣ 3 := by
      rw [← h.orderOf_a]
      exact orderOf_dvd_of_mem_zpowers ht_z
    have hdvd1 : orderOf t ∣ 1 := by
      have hg := Nat.dvd_gcd hdvd2 hdvd3
      rwa [show Nat.gcd 2 3 = 1 by decide] at hg
    exact h.t_ne_one (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1))
  exact false_of_quotient_data hGH (hK.quotient (zpowers a)) (odd_normal_quot h)
    (card_two_subgroup_le_quot h.orderOf_a h.Y_sylow) hFp hFz hPF hPcard hPA8 hx2 hx1
    (card_centralizer_quot h) hMC hMp hM hIcard hI hJ

end CFSG.EvenSporadicStandard.HNRecog.Harada
