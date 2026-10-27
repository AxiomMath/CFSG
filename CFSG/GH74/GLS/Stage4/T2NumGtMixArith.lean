module

public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem ng_val2_pow_sq_sub_one {p m : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) (hm : m ≠ 0) :
    padicValNat 2 (p ^ (2 * m) - 1) = padicValNat 2 (p + 1) + padicValNat 2 (p - 1) + padicValNat 2 m := by
  have h2 : ¬ 2 ∣ p := by
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := hp
    omega
  have hpm : p ^ (2 * m) - 1 ^ (2 * m) = p ^ (2 * m) - 1 := by rw [one_pow]
  have h := padicValNat.pow_two_sub_pow (x := p) (y := 1) (by omega) (by
    obtain ⟨j, hj⟩ := hp; exact ⟨j, by omega⟩) h2 (n := 2 * m) (by omega) (by exact even_two_mul m)
  rw [one_pow] at h
  have h2m : padicValNat 2 (2 * m) = 1 + padicValNat 2 m := by
    rw [padicValNat.mul (by norm_num) hm]
    simp
  omega

theorem ng_pow_mod_four {p : ℕ} (hp : Odd p) (m : ℕ) : p ^ m % 4 = p ^ (m % 2) % 4 := by
  have hsq : p ^ 2 % 4 = 1 := by
    obtain ⟨j, rfl⟩ := hp
    have : (2 * j + 1) ^ 2 = 4 * (j * j + j) + 1 := by ring
    omega
  conv_lhs => rw [← Nat.div_add_mod m 2, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hsq]
  simp

theorem mixed_not_pow {q₁ q₂ p m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq₁ : q₁ = p ^ m) (hq₂ : q₂ = p ^ n)
    (hm : m ≠ 0) (hn : n ≠ 0) (hv : ∀ k : ℕ, 2 ^ k ∣ q₁ ^ 2 - 1 ↔ 2 ^ k ∣ q₂ ^ 2 - 1) :
    q₁ % 4 = q₂ % 4 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have e1 : q₁ ^ 2 - 1 = p ^ (2 * m) - 1 := by rw [hq₁, ← pow_mul, mul_comm]
  have e2 : q₂ ^ 2 - 1 = p ^ (2 * n) - 1 := by rw [hq₂, ← pow_mul, mul_comm]
  have hne₁ : p ^ (2 * m) - 1 ≠ 0 := by
    have : 1 < p ^ (2 * m) := Nat.one_lt_pow (by omega) (by omega)
    omega
  have hne₂ : p ^ (2 * n) - 1 ≠ 0 := by
    have : 1 < p ^ (2 * n) := Nat.one_lt_pow (by omega) (by omega)
    omega
  have hval : padicValNat 2 (p ^ (2 * m) - 1) = padicValNat 2 (p ^ (2 * n) - 1) := by
    rw [e1] at hv
    rw [e2] at hv
    apply le_antisymm
    · exact (padicValNat_dvd_iff_le hne₂).1 ((hv _).1 pow_padicValNat_dvd)
    · exact (padicValNat_dvd_iff_le hne₁).1 ((hv _).2 pow_padicValNat_dvd)
  rw [ng_val2_pow_sq_sub_one hpodd hp3 hm, ng_val2_pow_sq_sub_one hpodd hp3 hn] at hval
  have hmn : padicValNat 2 m = padicValNat 2 n := by omega
  have hpar : m % 2 = n % 2 := by
    have key : ∀ k : ℕ, k ≠ 0 → (padicValNat 2 k = 0 ↔ k % 2 = 1) := by
      intro k hk
      rw [padicValNat.eq_zero_iff]
      constructor
      · rintro (h | h | h)
        · omega
        · exact absurd h hk
        · omega
      · intro h; right; right; omega
    have h1 := key m hm
    have h2 := key n hn
    omega
  rw [hq₁, hq₂, ng_pow_mod_four hpodd m, ng_pow_mod_four hpodd n, hpar]

theorem mixed_five_three {q₁ p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hodd : Odd q₁) (h5 : 5 ≤ q₁)
    (hlt : p < q₁) (h9 : q₁ ≤ 9) (hdvd : p ∣ q₁ ^ 2 - 1) (hmod : q₁ % 4 ≠ p % 4) :
    q₁ = 5 ∧ p = 3 := by
  obtain ⟨j, hj⟩ := hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  interval_cases q₁ <;> interval_cases p <;>
    first | omega | (exact absurd hp (by decide))

end CFSG.GH74.GLS.Stage4.Rest
