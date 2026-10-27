module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fx_qe_pow_four_mem {G : Type} [Group G] {C : Subgroup G} {x : G}
    (hdvd : C.relIndex (zpowers x) ∣ 8)
    (hnc : C.relIndex (zpowers x) = 8 →
      ∃ a ∈ zpowers x, ∃ b ∈ zpowers x, a * b * a⁻¹ * b⁻¹ ∉ C) : x ^ 4 ∈ C := by
  haveI : (C.subgroupOf (zpowers x)).Normal := inferInstance
  have hxmem : x ^ (C.subgroupOf (zpowers x)).index ∈ C := by
    have h := Subgroup.pow_index_mem (C.subgroupOf (zpowers x))
      (⟨x, Subgroup.mem_zpowers x⟩ : zpowers x)
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have hne : C.relIndex (zpowers x) ≠ 8 := by
    intro h8
    obtain ⟨a, ha, b, hb, hab⟩ := hnc h8
    apply hab
    obtain ⟨m, rfl⟩ := (Subgroup.mem_zpowers_iff).mp ha
    obtain ⟨k, rfl⟩ := (Subgroup.mem_zpowers_iff).mp hb
    have hcomm : Commute (x ^ m) (x ^ k) := Commute.zpow_zpow_self x m k
    rw [hcomm.mul_inv_cancel, mul_inv_cancel]
    exact C.one_mem
  have hdvd4 : C.relIndex (zpowers x) ∣ 4 := by
    have hdvd' : C.relIndex (zpowers x) ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by decide]
      exact hdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hk2 : k ≤ 2 := by
      by_contra h
      have hk3 : 3 ≤ k := Nat.succ_le_of_lt (not_le.mp h)
      have hk_eq : k = 3 := le_antisymm hk hk3
      exact hne (by rw [hk', hk_eq]; decide)
    rw [hk']
    exact (Nat.dvd_prime_pow Nat.prime_two).mpr ⟨k, hk2, rfl⟩
  obtain ⟨c, hc⟩ := hdvd4
  rw [hc, pow_mul]
  exact C.pow_mem hxmem c

end CFSG.OddStandard.SmallF3.Omega
