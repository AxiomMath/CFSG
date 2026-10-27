module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FiveLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.GammaCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma isConj_orderOf_eq {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have h' := MulEquiv.orderOf_eq (MulAut.conj c) x
  simp only [MulAut.conj_apply] at h'
  rw [hc] at h'
  exact h'.symm

theorem not_dvd_card_Gxy_of_odd (hU : U35Facts) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hGam : GammaFacts a z) (hT7 : TableVIIFacts a z) (hFive : FiveFacts a z) {x : G}
    (hx : IsConj a x) (hne : x ≠ a) (hodd : Odd (orderOf (a * x))) :
    ¬ 11 ∣ Nat.card ↥(Gxy a x) := by
  have hxmem : x ∈ gammaSet a z a := hGam.eq_gamma a x (IsConj.refl a) hx
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc] at hxmem
  rcases hxmem with hxa | hx2A | hx2B | hx3A | hx4A | hx4B | hx5A | hx5E | hx6A
  · exact absurd hxa hne
  · exfalso
    have h2 : orderOf (a * x) = 2 := by rw [← isConj_orderOf_eq hx2A.2, h.orderOf_a]
    exact hodd.not_two_dvd_nat (by rw [h2])
  · exfalso
    have h2 : orderOf (a * x) = 2 := by rw [← isConj_orderOf_eq hx2B.2, h.orderOf_z]
    exact hodd.not_two_dvd_nat (by rw [h2])
  · rw [Gxy_eq_inf, hT7.card_3A x hx3A]
    norm_num
  · exfalso
    have h2 : orderOf ((a * x) ^ 2) = 2 := by rw [← isConj_orderOf_eq hx4A.2, h.orderOf_z]
    have hdvd : 2 ∣ orderOf (a * x) :=
      dvd_trans (by rw [h2]) (orderOf_pow_dvd (x := a * x) 2)
    exact hodd.not_two_dvd_nat hdvd
  · exfalso
    have h2 : orderOf ((a * x) ^ 2) = 2 := by rw [← isConj_orderOf_eq hx4B.2, h.orderOf_a]
    have hdvd : 2 ∣ orderOf (a * x) :=
      dvd_trans (by rw [h2]) (orderOf_pow_dvd (x := a * x) 2)
    exact hodd.not_two_dvd_nat hdvd
  · have hcard : Nat.card ↥(Gxy a x) = 126000 := hU.card_eq ↥(Gxy a x) (hT7.shape_5A x hx5A)
    rw [hcard]
    norm_num
  · have hcard : Nat.card ↥(Gxy a x) = 500 :=
      card_eq_of_isShapeFiveCubeByTwoTwo (hFive.five_E x hx5E)
    rw [hcard]
    norm_num
  · exfalso
    have hdvd : 2 ∣ orderOf (a * x) := by rw [hx6A.2.1]; norm_num
    exact hodd.not_two_dvd_nat hdvd

end CFSG.EvenSporadicStandard.HNRecog.Section3
