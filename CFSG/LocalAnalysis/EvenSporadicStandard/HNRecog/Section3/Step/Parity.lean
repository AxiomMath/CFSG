module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma pow_two_eq_one_of_isConj {G : Type} [Group G] {a x : G} (ha : orderOf a = 2)
    (hx : IsConj a x) : x ^ 2 = 1 := by
  have ho : orderOf x = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    rw [← hc, ← MulAut.conj_apply c a, MulEquiv.orderOf_eq, ha]
  rw [← ho]
  exact pow_orderOf_eq_one x

private lemma conj_pow_of_odd_order {G : Type} [Group G] {a x : G} (ha2 : a ^ 2 = 1)
    (hx2 : x ^ 2 = 1) {m : ℕ} (hm : (a * x) ^ (2 * m + 1) = 1) :
    (a * x) ^ m * a * ((a * x) ^ m)⁻¹ = x := by
  have ha_mul : a * a = 1 := by simpa [pow_two] using ha2
  have hx_mul : x * x = 1 := by simpa [pow_two] using hx2
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha_mul
  have hx_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx_mul
  have har : a * (a * x) * a⁻¹ = (a * x)⁻¹ := by
    rw [mul_inv_rev, ha_inv, hx_inv, ← mul_assoc a a x, ha_mul, one_mul]
  have hr_2m : (a * x) ^ (2 * m) = (a * x)⁻¹ := by
    have h : (a * x) ^ (2 * m) * (a * x) = 1 := by rw [← pow_succ, hm]
    exact eq_inv_of_mul_eq_one_left h
  have hu : a * (a * x) ^ m * a⁻¹ = ((a * x) ^ m)⁻¹ := by
    rw [← conj_pow (a := a) (b := a * x) (i := m), har, inv_pow]
  have hzu : a⁻¹ * (a * x) ^ m * a = ((a * x) ^ m)⁻¹ := by
    simpa [ha_inv] using hu
  have hu2 : ((a * x) ^ m)⁻¹ * ((a * x) ^ m)⁻¹ = a * x := by
    rw [← mul_inv_rev, ← sq, ← pow_mul, Nat.mul_comm, hr_2m, inv_inv]
  calc (a * x) ^ m * a * ((a * x) ^ m)⁻¹
      = a * (a⁻¹ * (a * x) ^ m * a) * ((a * x) ^ m)⁻¹ := by group
    _ = a * (((a * x) ^ m)⁻¹) * ((a * x) ^ m)⁻¹ := by rw [hzu]
    _ = a * (((a * x) ^ m)⁻¹ * ((a * x) ^ m)⁻¹) := by group
    _ = a * (a * x) := by rw [hu2]
    _ = x := by rw [← mul_assoc, ha_mul, one_mul]

theorem parity_of_fusion3 {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) : ParityFacts a z := by
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  refine ⟨?_, ?_⟩
  · intro x t hx _ht2 htmem hnot
    have hx2 : x ^ 2 = 1 := pow_two_eq_one_of_isConj h.orderOf_a hx
    have hta : a * t = t * a := mem_Gx.mp (mem_Gxy.mp htmem).1
    have htx : x * t = t * x := mem_Gx.mp (mem_Gxy.mp htmem).2
    rw [← Nat.not_odd_iff_even]
    rintro ⟨m, hm⟩
    have hr_pow : (a * x) ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
    have hxa := conj_pow_of_odd_order (a := a) (x := x) ha2 hx2 (m := m) hr_pow
    have hrt : Commute (a * x) t := by
      rw [commute_iff_eq]
      calc (a * x) * t = a * (x * t) := mul_assoc a x t
        _ = a * (t * x) := by rw [htx]
        _ = (a * t) * x := (mul_assoc a t x).symm
        _ = (t * a) * x := by rw [hta]
        _ = t * (a * x) := mul_assoc t a x
    have hcomm : (a * x) ^ m * t * ((a * x) ^ m)⁻¹ = t := by
      rw [(hrt.pow_left m).eq]
      group
    have hconj : IsConj (a * t) (x * t) := by
      refine isConj_iff.mpr ⟨(a * x) ^ m, ?_⟩
      calc (a * x) ^ m * (a * t) * ((a * x) ^ m)⁻¹
          = ((a * x) ^ m * a * ((a * x) ^ m)⁻¹) *
              ((a * x) ^ m * t * ((a * x) ^ m)⁻¹) := by group
        _ = x * t := by rw [hxa, hcomm]
    exact hnot hconj
  · intro x t hx ht htG
    have hx2 : x ^ 2 = 1 := pow_two_eq_one_of_isConj h.orderOf_a hx
    have hx_mul : x * x = 1 := by simpa [pow_two] using hx2
    have htx : x * t = t * x := mem_Gx.mp (mem_Gxy.mp htG).2
    have haQ : a ∈ Qz t := ((hF3.self).shape_2AB t ht).2
    have hxQ : x * a * x⁻¹ ∈ Qz t := by
      have h2 : x * t * x⁻¹ = t := by rw [htx]; group
      simpa [h2] using Qz_conj_mem x haQ
    have hx2' : (a * x) ^ 2 = a * (x * a * x⁻¹) := by
      rw [pow_two]
      calc (a * x) * (a * x) = a * (x * a * x⁻¹) * (x * x) := by group
        _ = a * (x * a * x⁻¹) * 1 := by rw [hx_mul]
        _ = a * (x * a * x⁻¹) := by rw [mul_one]
    have hQ : (a * x) ^ 2 ∈ Qz t := by
      rw [hx2']
      exact (Qz t).mul_mem haQ hxQ
    have hpQ : IsPGroup 2 ↥(Qz t) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx t))).map (Gx t).subtype
    obtain ⟨j, hj⟩ := hpQ.exists_orderOf_eq_pow ⟨(a * x) ^ 2, hQ⟩
    have horder2 : orderOf ((a * x) ^ 2) = 2 ^ j := by
      simpa using (Subgroup.orderOf_coe (⟨(a * x) ^ 2, hQ⟩ : ↥(Qz t))).trans hj
    have hdvd : orderOf (a * x) ∣ 2 ^ (j + 1) := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_succ']
      calc (a * x) ^ (2 * 2 ^ j) = ((a * x) ^ 2) ^ (2 ^ j) := pow_mul (a * x) 2 (2 ^ j)
        _ = 1 := by
          rw [← horder2]
          exact pow_orderOf_eq_one _
    obtain ⟨k, _hk, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
