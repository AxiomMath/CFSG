module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.InvDerived
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem orderOf_eq_of_isConj {G : Type} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

theorem not_mem_derivedOf_of_isConj (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) {b : G} (hb : IsConj a b)
    (hab : IsConj a (a * b)) (hne : b ≠ a) : b ∉ derivedOf (Gx a) := by
  intro hb'
  have hb2 : orderOf b = 2 := by rw [← orderOf_eq_of_isConj hb, h.orderOf_a]
  rcases inv_mem_derivedOf_cases hI h hF1 hb' hb2 with hba | ⟨hzb, -, -⟩ | ⟨hab', hzab⟩
  · exact hne hba
  · exact not_isConj_of_isF5Type hI h (hb.trans hzb.symm)
  · exact not_isConj_of_isF5Type hI h (hab.trans hzab.symm)

theorem mem_Qz_of_isConj_mul (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) {x t : G} (hx : IsConj a x) (ht : IsConj z t)
    (hxt : x * t = t * x) (hxt' : IsConj a (x * t)) : x ∈ Qz t := by
  have hxt0 : IsF5Type x t := isF5Type_of_isConj h hx ht
  have hFx : Fusion1Facts x t := hF1 x t hx ht
  have ht2 : orderOf t = 2 := by rw [← orderOf_eq_of_isConj ht, h.orderOf_z]
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have htGx : t ∈ Gx x := mem_Gx.mpr hxt
  have hconj_xt : IsConj x (x * t) := hx.symm.trans hxt'
  have htm : t ∈ derivedOf (Gx x) :=
    hFx.derived_of_2B t htGx ht2' (IsConj.refl t) hconj_xt
  rcases inv_mem_derivedOf_cases hI hxt0 hFx htm ht2 with htx | ⟨-, -, hxQ⟩ | ⟨hxtc, -⟩
  · exact (not_isConj_of_isF5Type hI h (hx.trans (htx ▸ ht.symm))).elim
  · exact hxQ
  · exact (not_isConj_of_isF5Type hI h ((hx.trans hxtc).trans ht.symm)).elim

end CFSG.EvenSporadicStandard.HNRecog.Section3
