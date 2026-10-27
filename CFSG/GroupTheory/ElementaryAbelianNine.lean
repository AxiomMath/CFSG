module

import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GroupTheory

open scoped Pointwise

variable {R : Type*} [CommGroup R] [Finite R]

theorem sq_ne_one_of_mem_card_three {N : Subgroup R} (hN : Nat.card ↥N = 3) {x : R}
    (hx : x ∈ N) (hx1 : x ≠ 1) : x ^ 2 ≠ 1 := by
  intro hx2
  have hdvd : orderOf x ∣ Nat.card ↥N := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
  rw [hN] at hdvd
  have h2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
  have h1 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h2 hdvd
    simpa using this
  exact hx1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))

theorem eq_left_or_right_of_aut_inverts_fixes {A B N : Subgroup R}
    (hA : Nat.card ↥A = 3) (hB : Nat.card ↥B = 3) (hN : Nat.card ↥N = 3)
    (hdisj : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤)
    (φ : MulAut R) (hφA : ∀ a ∈ A, φ a = a⁻¹) (hφB : ∀ b ∈ B, φ b = b)
    (hφN : ∀ n ∈ N, φ n ∈ N) : N = A ∨ N = B := by
  classical
  obtain ⟨n, hn, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      simpa using h x hx
    rw [hbot] at hN
    simp at hN
  have hzp : Subgroup.zpowers n = N :=
    (CFSG.RankThree.PartTwo.Sec17.Proof176Steps.eq_zpowers_of_card_three hN hn hn1).symm
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Subgroup.mem_sup.mp (by rw [hsup]; exact Subgroup.mem_top n)
  rcases eq_or_ne a 1 with rfl | ha1
  ·
    right
    have hnb : n = b := by rw [← hab]; simp
    have hb1 : b ≠ 1 := by rw [← hnb]; exact hn1
    have hbzp : Subgroup.zpowers b = B :=
      (CFSG.RankThree.PartTwo.Sec17.Proof176Steps.eq_zpowers_of_card_three hB hb hb1).symm
    rw [hnb, hbzp] at hzp
    exact hzp.symm
  rcases eq_or_ne b 1 with rfl | hb1
  ·
    left
    have hna : n = a := by rw [← hab]; simp
    have ha1' : a ≠ 1 := by rw [← hna]; exact hn1
    have hazp : Subgroup.zpowers a = A :=
      (CFSG.RankThree.PartTwo.Sec17.Proof176Steps.eq_zpowers_of_card_three hA ha ha1').symm
    rw [hna, hazp] at hzp
    exact hzp.symm
  exfalso
  have hφn : φ n = a⁻¹ * b := by
    rw [← hab, map_mul, hφA a ha, hφB b hb]
  have hn3 : n ^ 3 = 1 := by
    have hdvd : orderOf n ∣ Nat.card ↥N := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hn)
    rw [hN] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hn1
    · exact orderOf_dvd_iff_pow_eq_one.mp (h ▸ dvd_rfl)
  have hcases : φ n = 1 ∨ φ n = n ∨ φ n = n ^ 2 := by
    have hmem : φ n ∈ Subgroup.zpowers n := by rw [hzp]; exact hφN n hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hk, zpow_eq_zpow_emod' (x := n) k hn3]
    have hnonneg : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
    have htoNat : (((k % ((3 : ℕ) : ℤ)).toNat : ℤ)) = k % ((3 : ℕ) : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    rw [← htoNat, zpow_natCast]
    set m := (k % ((3 : ℕ) : ℤ)).toNat with hm
    have hlt : m < 3 := by
      have h1 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < ((3 : ℕ) : ℤ))
      omega
    interval_cases m
    · left; norm_num
    · right; left; norm_num
    · right; right; norm_num

  have hneq1 : a⁻¹ * b ≠ 1 := by
    intro h
    have hab' : a = b := by
      have hb : b = a := by
        calc b = a * (a⁻¹ * b) := by group
          _ = a * 1 := by rw [h]
          _ = a := by group
      exact hb.symm
    have : a ∈ A ⊓ B := ⟨ha, hab' ▸ hb⟩
    rw [hdisj] at this
    exact ha1 (Subgroup.mem_bot.mp this)
  rcases hcases with h1 | h1 | h2
  · exact hneq1 (hφn.symm.trans h1)
  · have hEq : a⁻¹ * b = a * b := by
      rw [hab]
      exact hφn.symm.trans h1
    have haa : a⁻¹ = a := mul_right_cancel hEq
    refine sq_ne_one_of_mem_card_three hA ha ha1 ?_
    calc a ^ 2 = a * a := by rw [pow_two]
      _ = a * a⁻¹ := by rw [haa]
      _ = 1 := mul_inv_cancel a
  · have hEq : a⁻¹ * b = a * b * a * b := by
      have h2' : a⁻¹ * b = n ^ 2 := hφn.symm.trans h2
      calc a⁻¹ * b = n ^ 2 := h2'
        _ = n * n := by rw [pow_two]
        _ = a * b * (a * b) := by rw [hab]
        _ = a * b * a * b := by ac_rfl
    have hEq' : a⁻¹ * b = a * a * b * b := by rw [hEq]; ac_rfl
    have hb_eq : a⁻¹ = a * a * b := mul_right_cancel (by
      rw [mul_assoc, hEq', mul_assoc, mul_assoc])
    have ha3 : a * a * a = 1 := by
      have hdvd : orderOf a ∣ Nat.card ↥A := by
        rw [← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ha)
      rw [hA] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) ha1
      · have h3 : a ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [h])
        simpa [pow_succ, pow_two, mul_assoc] using h3
    have hb1' : b = 1 := by
      calc b = (a * a)⁻¹ * (a * a * b) := by group
        _ = (a * a)⁻¹ * a⁻¹ := by rw [← hb_eq]
        _ = (a * a * a)⁻¹ := by group
        _ = 1 := by rw [ha3, inv_one]
    exact hb1 hb1'

end CFSG.GroupTheory

end
