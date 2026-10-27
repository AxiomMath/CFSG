module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.InvDerived
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem isConj_z_mul_of_isConj_a (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) {v t : G}
    (hv : IsConj a v) (ht : t ∈ derivedOf (Gx v)) (htv : t ≠ v) (hta : IsConj a t) :
    IsConj z (v * t) := by
  have hv' : IsF5Type v z := isF5Type_of_isConj h hv (IsConj.refl z)
  have hF1v : Fusion1Facts v z := hF1 v z hv (IsConj.refl z)
  have hF2v : Fusion2Facts v z := hF2 v z hv (IsConj.refl z)
  have hv_ord : orderOf v = 2 := hv'.orderOf_a
  have hv2 : v ^ 2 = 1 := by rw [← hv_ord]; exact pow_orderOf_eq_one v
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have htGx : t ∈ Gx v := derivedOf_le (Gx v) ht
  have ht2 : t ^ 2 = 1 := by
    have hpow := IsConj.pow 2 hta
    rw [ha2] at hpow
    exact isConj_one_right.mp hpow
  have hvt : IsConj v t := hv.symm.trans hta
  have hnot : ¬ IsConj v (v * t) :=
    ((hF2v.mem_derived_iff t htGx ht2).mp ht).mp hvt
  have hvht : v * t ∈ derivedOf (Gx v) := (derivedOf (Gx v)).mul_mem (mem_derivedOf_self hF1v) ht
  have hcomm : Commute v t := (commute_iff_eq v t).mpr (mem_Gx.mp htGx)
  have hvt2 : (v * t) ^ 2 = 1 := by rw [hcomm.mul_pow, hv2, ht2, one_mul]
  have hvt_ne_one : v * t ≠ 1 := by
    intro h1
    have ht_eq : t = v := by
      calc t = v⁻¹ * (v * t) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = v⁻¹ * 1 := by rw [h1]
        _ = v := by rw [mul_one, inv_eq_self_of_orderOf_eq_two hv_ord]
    exact htv ht_eq
  have hvt_ord : orderOf (v * t) = 2 := orderOf_eq_prime hvt2 hvt_ne_one
  rcases inv_mem_derivedOf_cases hI hv' hF1v hvht hvt_ord with h1 | h2 | h3
  ·
    exfalso
    have ht1 : t = 1 := mul_left_cancel (by rw [h1, mul_one])
    have ha1 : a = 1 := isConj_one_left.mp (by rw [← ht1]; exact hta)
    have hord := h.orderOf_a
    rw [ha1, orderOf_one] at hord
    exact absurd hord (by decide)
  · exact h2.1
  · exact absurd h3.1 hnot

theorem isConj_a_mul_of_isConj_z (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) {v t : G}
    (hv : IsConj a v) (ht : t ∈ derivedOf (Gx v)) (htz : IsConj z t) : IsConj a (v * t) := by
  have hF2v : Fusion2Facts v z := hF2 v z hv (IsConj.refl z)
  have htGx : t ∈ Gx v := derivedOf_le (Gx v) ht
  have hz2 : z ^ 2 = 1 := by rw [← h.orderOf_z]; exact pow_orderOf_eq_one z
  have ht2 : t ^ 2 = 1 := by
    have hpow := IsConj.pow 2 htz
    rw [hz2] at hpow
    exact isConj_one_right.mp hpow
  have hiff := (hF2v.mem_derived_iff t htGx ht2).mp ht
  have hnot : ¬ IsConj v t := by
    intro hvt
    exact not_isConj_of_isF5Type hI h (hv.trans (hvt.trans htz.symm))
  have hvt' : IsConj v (v * t) := by
    by_contra hcon
    exact hnot (hiff.mpr hcon)
  exact hv.trans hvt'

end CFSG.EvenSporadicStandard.HNRecog.Section3
