module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three {w x : G} (hw : orderOf w = 3)
    (hx : x ∈ Subgroup.zpowers w) (hx1 : x ≠ 1) : x = w ∨ x = w⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hw3n : w ^ 3 = 1 := by
    rw [← hw]
    exact pow_orderOf_eq_one w
  have hw3 : w ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hw3n
  have hw2 : w ^ 2 = w⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ', show 2 + 1 = 3 by norm_num]
    exact hw3n
  rw [zpow_eq_zpow_emod (x := w) k hw3] at hx1 ⊢
  set r : ℤ := k % 3 with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg k (by norm_num)
  have hr3 : r < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hne0 : r ≠ 0 := by
    intro h0
    apply hx1
    rw [h0]
    simp
  have hcases : r = 1 ∨ r = 2 := by
    interval_cases r <;> simp_all
  rcases hcases with h1 | h2
  · left
    rw [h1]
    simp
  · right
    rw [h2]
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hw2

theorem mem_or_inv_mul_mem_or_mul_mem_of_relIndex_eq_three {P S : Subgroup G}
    (hSn : (S.subgroupOf P).Normal) (hSidx : S.relIndex P = 3) {y : G} (hyP : y ∈ P)
    (hyS : y ∉ S) {x : G} (hxP : x ∈ P) : x ∈ S ∨ y⁻¹ * x ∈ S ∨ y * x ∈ S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let N : Subgroup P := S.subgroupOf P
  haveI : N.Normal := hSn
  let π : P →* P ⧸ N := QuotientGroup.mk' N
  have hcard : Nat.card (P ⧸ N) = 3 := by
    rw [← Subgroup.index_eq_card N]
    exact hSidx
  let yP : P := ⟨y, hyP⟩
  let xP : P := ⟨x, hxP⟩
  have hyq_ne : π yP ≠ 1 := by
    intro hq
    have hmem : yP ∈ N := (QuotientGroup.eq_one_iff yP).mp hq
    exact hyS (by simpa [N, Subgroup.mem_subgroupOf] using hmem)
  have hdvd : orderOf (π yP) ∣ Nat.card (P ⧸ N) := orderOf_dvd_natCard _
  rw [hcard] at hdvd
  have hne1 : orderOf (π yP) ≠ 1 := by
    intro h1
    exact hyq_ne (orderOf_eq_one_iff.mp h1)
  have hord : orderOf (π yP) = 3 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3)
      (orderOf (π yP)) hdvd with h1 | h3
    · exact absurd h1 hne1
    · exact h3
  have hzpcard : Nat.card (Subgroup.zpowers (π yP)) = 3 := by
    rw [Nat.card_zpowers, hord]
  haveI : Finite ↥(Subgroup.zpowers (π yP)) :=
    (Nat.card_ne_zero.mp (by rw [hzpcard]; norm_num)).2
  have htop : Subgroup.zpowers (π yP) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hzpcard, hcard]
  have hxmem : π xP ∈ Subgroup.zpowers (π yP) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hyq3 : (π yP) ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hyq3z : (π yP) ^ (3 : ℤ) = 1 := by
    simpa using hyq3
  rw [zpow_eq_zpow_emod (x := π yP) k hyq3z] at hk
  set r : ℤ := k % 3 with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg k (by norm_num)
  have hr3 : r < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by
    interval_cases r <;> simp
  have hmem_of_pi_eq_one : ∀ {z : G} (hz : z ∈ P), π ⟨z, hz⟩ = 1 → z ∈ S := by
    intro z hz hq
    have hmem : (⟨z, hz⟩ : P) ∈ N := (QuotientGroup.eq_one_iff _).mp hq
    exact (Subgroup.mem_subgroupOf).mp hmem
  rcases hcases with h0 | h1 | h2
  · left
    rw [h0] at hk
    exact hmem_of_pi_eq_one hxP (hk.symm.trans (by simp))
  · right; left
    rw [h1] at hk
    simp only [zpow_one] at hk
    have hq : π (yP⁻¹ * xP) = 1 := by
      rw [map_mul, map_inv, hk]
      simp
    have hmem := hmem_of_pi_eq_one (P.mul_mem (P.inv_mem hyP) hxP) hq
    simpa using hmem
  · right; right
    rw [h2] at hk
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two] at hk
    have hq : π (yP * xP) = 1 := by
      rw [map_mul, ← hk, ← pow_three]
      exact hyq3
    have hmem := hmem_of_pi_eq_one (P.mul_mem hyP hxP) hq
    simpa using hmem

end CFSG.GroupTheory
