module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG.LocalAnalysis.ComponentInitial

section Nat

theorem u6r_pow_mod_three {f : ℕ} (hf : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end Nat

section Field

variable {f : ℕ} {K : Type} [Field K]

theorem u6r_bar_mul_self (h : UnitaryFieldData 2 f K) (hf : Odd f) {d : K} (hd : d ^ 3 = 1) :
    h.bar d * d = 1 := by
  rw [h.bar_apply, ← Nat.div_add_mod (2 ^ f) 3, u6r_pow_mod_three hf, pow_add, pow_mul, hd,
    one_pow, one_mul, ← pow_succ]
  exact hd

theorem u6r_pow_succ_eq_one_of_cube (h : UnitaryFieldData 2 f K) (hf : Odd f) {a : Kˣ}
    (ha : (a ^ 3) ^ (2 ^ f + 1) = 1) : a ^ (2 ^ f + 1) = 1 := by
  have h3 := u6r_pow_mod_three hf
  have hr1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hcard : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, h.card, pow_mul']
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ f = s + 1 := ⟨2 ^ f - 1, by omega⟩
    rw [hs, Nat.add_sub_cancel]
    have : (s + 1) ^ 2 = (s + 1 + 1) * s + 1 := by ring
    omega
  have hcop : Nat.Coprime 3 (2 ^ f - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  refine (pow_eq_one_iff_of_coprime hcop).mp ⟨?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    exact ha
  · rw [← pow_mul, ← hcard]
    exact pow_card_eq_one'

theorem u6r_exists_mul_cube (h : UnitaryFieldData 2 f K) {μ : Kˣ} (hμ : ∀ a : Kˣ, a ^ 3 ≠ μ)
    (ν : Kˣ) : ∃ j : ℕ, j < 3 ∧ ∃ a : Kˣ, a ^ 3 = ν * μ ^ j := by
  have := h.finite
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hpow : ∀ x : Kˣ, ∃ m : ℕ, γ ^ m = x := fun x =>
    (Submonoid.mem_powers_iff x γ).mp (mem_powers_iff_mem_zpowers.mpr (hγ x))
  have hcube : ∀ t : ℕ, 3 ∣ t → ∃ a : Kˣ, a ^ 3 = γ ^ t := by
    rintro t ⟨s, rfl⟩
    exact ⟨γ ^ s, by rw [← pow_mul, mul_comm]⟩
  obtain ⟨m, rfl⟩ := hpow μ
  obtain ⟨k, rfl⟩ := hpow ν
  have hm : ¬ 3 ∣ m := fun hm => by
    obtain ⟨a, ha⟩ := hcube m hm
    exact hμ a ha
  have hdisj : 3 ∣ k ∨ 3 ∣ k + m ∨ 3 ∣ k + 2 * m := by
    have hm' : m % 3 = 1 ∨ m % 3 = 2 := by omega
    have hk' : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hm' with hm' | hm' <;> rcases hk' with hk' | hk' | hk' <;> omega
  rcases hdisj with hk | hk | hk
  · obtain ⟨a, ha⟩ := hcube k hk
    exact ⟨0, by norm_num, a, by rw [ha, pow_zero, mul_one]⟩
  · obtain ⟨a, ha⟩ := hcube (k + m) hk
    exact ⟨1, by norm_num, a, by rw [ha, pow_add, pow_one]⟩
  · obtain ⟨a, ha⟩ := hcube (k + 2 * m) hk
    exact ⟨2, by norm_num, a, by rw [ha, pow_add, pow_mul']⟩

theorem u6r_irreducible {μ : Kˣ} (hμ : ∀ a : Kˣ, a ^ 3 ≠ μ) :
    Irreducible (X ^ 3 - C (μ : K)) := by
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_three fun b hb => ?_
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact μ.ne_zero (by rw [← hb]; norm_num)
  exact hμ (Units.mk0 b hb0) (Units.ext (by simpa using hb))

theorem u6r_exists_primitive_cube_root (h : UnitaryFieldData 2 f K) :
    ∃ κ : K, κ ^ 3 = 1 ∧ κ ≠ 1 := by
  have := h.finite
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨(x : K), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one]
  · intro h1
    have hx1 : x = 1 := Units.ext h1
    rw [hx1, orderOf_one] at hx
    norm_num at hx

theorem u6r_one_add_add_sq {κ : K} (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1) : 1 + κ + κ ^ 2 = 0 := by
  have h0 : (κ - 1) * (1 + κ + κ ^ 2) = 0 := by linear_combination hκ3
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hκ1
  · exact h

theorem u6r_cube_root_cases {κ d : K} (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1) (hd : d ^ 3 = 1) :
    d = 1 ∨ d = κ ∨ d = κ ^ 2 := by
  have hsum := u6r_one_add_add_sq hκ3 hκ1
  have h0 : (d - 1) * (d - κ) * (d - κ ^ 2) = 0 := by
    linear_combination hd + (d - d ^ 2) * hsum + (d - 1) * hκ3
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem u6r_X_pow_three_sub_one {κ : K} (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1) :
    (X ^ 3 - 1 : K[X]) = (X - C 1) * (X - C κ) * (X - C (κ ^ 2)) := by
  have h1 := congrArg C (u6r_one_add_add_sq hκ3 hκ1)
  have h2 := congrArg C hκ3
  simp only [map_add, map_one, map_pow, map_zero] at h1 h2
  rw [map_one, map_pow]
  linear_combination (X ^ 2 - X) * h1 + (1 - X) * h2

end Field

end CFSG.HardMathSupport.Dickson.Sec6.I1431
