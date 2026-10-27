module

public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.GroupTheory

theorem sq_dvd_natCard_of_commute {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x y : G} (hx : orderOf x = p) (hy : orderOf y = p) (hxy : Commute x y)
    (hyx : y ∉ Subgroup.zpowers x) : p ^ 2 ∣ Nat.card G := by
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
  have hle : Subgroup.zpowers x ≤ C := Subgroup.zpowers_le.mpr hxC
  let N : Subgroup C := (Subgroup.zpowers x).subgroupOf C
  have hNnormal : N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hcomm : Commute k x := Subgroup.mem_centralizer_singleton_iff.mp hk
    have hcomm' : Commute k (x ^ m) := hcomm.zpow_right m
    rw [hcomm'.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
  have hNcard : Nat.card N = p := by
    have h1 : Nat.card N = Nat.card (Subgroup.zpowers x) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [h1, Nat.card_zpowers, hx]
  let yC : C := ⟨y, hyC⟩
  have hyCpow : yC ^ p = 1 := by
    ext
    simpa using (orderOf_eq_prime_iff.mp hy).1
  let qy : C ⧸ N := QuotientGroup.mk' N yC
  have hqypow : qy ^ p = 1 := by
    change ((QuotientGroup.mk' N) yC) ^ p = 1
    rw [← map_pow, hyCpow, map_one]
  have hqyne : qy ≠ 1 := by
    intro h1
    have hmem : y ∈ Subgroup.zpowers x := by
      have h1' : yC ∈ N := (QuotientGroup.eq_one_iff (N := N) yC).mp h1
      simpa [N] using (Subgroup.mem_subgroupOf.mp h1')
    exact hyx hmem
  have hqyord : orderOf qy = p := orderOf_eq_prime hqypow hqyne
  have hpquot : p ∣ Nat.card (C ⧸ N) := by
    rw [← hqyord]
    exact orderOf_dvd_natCard qy
  have hppC : p ^ 2 ∣ Nat.card C := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hNcard, pow_two]
    exact mul_dvd_mul hpquot dvd_rfl
  exact dvd_trans hppC (Subgroup.card_subgroup_dvd_card C)

end CFSG.GroupTheory
