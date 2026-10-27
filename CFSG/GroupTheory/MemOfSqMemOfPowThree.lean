module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG

theorem mem_of_mul_mem_of_sq_mem_of_pow_three {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {x y z : G} (hxy : x = y * z) (hz : z ∈ H) (hy : y ^ 2 ∈ H) (hx : x ^ 3 = 1) : x ∈ H := by
  rw [← QuotientGroup.eq_one_iff (x := x)]
  have hz1 : QuotientGroup.mk' H z = 1 := (QuotientGroup.eq_one_iff z).2 hz
  have hy2 : QuotientGroup.mk' H (y ^ 2) = 1 := (QuotientGroup.eq_one_iff (y ^ 2)).2 hy
  have hqy : (QuotientGroup.mk' H y) ^ 2 = 1 := by
    rw [← map_pow]
    exact hy2
  have hqx : QuotientGroup.mk' H x = QuotientGroup.mk' H y := by
    rw [hxy, map_mul, hz1, mul_one]
  have hqy3 : (QuotientGroup.mk' H y) ^ 3 = 1 := by
    rw [← hqx, ← map_pow, hx, map_one]
  have hdvd2 : orderOf (QuotientGroup.mk' H y) ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 hqy
  have hdvd3 : orderOf (QuotientGroup.mk' H y) ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hqy3
  have hone : orderOf (QuotientGroup.mk' H y) = 1 := by
    have h := Nat.dvd_gcd hdvd2 hdvd3
    simpa using h
  have hy1 : QuotientGroup.mk' H y = 1 := orderOf_eq_one_iff.1 hone
  exact hqx.trans hy1

end CFSG

end
