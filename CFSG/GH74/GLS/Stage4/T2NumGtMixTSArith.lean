module

public import CFSG.GH74.GLS.Stage4.T2NumGtTwoPart

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG CFSG.GH74.GLS.Stage4 CFSG.Assembly.LowTwoRank

theorem mix_pow_dvd_sq_sub_one {q : ℕ} (hq : q % 4 = 3) (k : ℕ) :
    2 ^ (k + 1) ∣ q ^ 2 - 1 ↔ 2 ^ k ∣ q + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, q = 4 * j + 3 := ⟨q / 4, by omega⟩
  have h1 : (4 * j + 3) ^ 2 - 1 = 2 * (4 * (j + 1)) * (2 * j + 1) := by
    have : (4 * j + 3) ^ 2 = 2 * (4 * (j + 1)) * (2 * j + 1) + 1 := by ring
    omega
  have h2 : 4 * j + 3 + 1 = 4 * (j + 1) := by omega
  rw [h1, h2]
  have hcop : Nat.Coprime (2 ^ (k + 1)) (2 * j + 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact odd_two_mul_add_one j
  rw [Nat.Coprime.dvd_mul_right hcop, pow_succ, mul_comm (2 ^ k) 2]
  exact Nat.mul_dvd_mul_iff_left (by norm_num)

theorem mix_pow_dvd_of_mod_four_two {m : ℕ} (hm : m % 4 = 2) (k : ℕ) : 2 ^ k ∣ m ↔ k ≤ 1 := by
  constructor
  · intro hd
    by_contra hk
    push Not at hk
    have h4 : 4 ∣ 2 ^ k := by
      have : (2 : ℕ) ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      simpa using this
    have := dvd_trans h4 hd
    omega
  · intro hk
    have : 2 ^ k ∣ 2 := by
      interval_cases k <;> simp
    exact dvd_trans this (by omega)

theorem t5_two_part_mix {q₁ q₂ : ℕ} (ho₁ : Odd q₁) (ho₂ : Odd q₂)
    (hsq : ∀ k : ℕ, 2 ^ k ∣ q₁ ^ 2 - 1 ↔ 2 ^ k ∣ q₂ ^ 2 - 1) (hmod : q₁ % 4 ≠ q₂ % 4) :
    ∀ k : ℕ, 2 ^ k ∣ q₁ + 1 ↔ 2 ^ k ∣ q₂ - 1 := by
  have hq₁4 : q₁ % 4 = 1 ∨ q₁ % 4 = 3 := by rcases ho₁ with ⟨k, hk⟩; omega
  have hq₂4 : q₂ % 4 = 1 ∨ q₂ % 4 = 3 := by rcases ho₂ with ⟨k, hk⟩; omega
  intro k
  rcases hq₁4 with h1 | h3
  ·
    have h3' : q₂ % 4 = 3 := by omega
    rw [mix_pow_dvd_of_mod_four_two (m := q₁ + 1) (by omega),
      mix_pow_dvd_of_mod_four_two (m := q₂ - 1) (by omega)]
  ·
    have h1' : q₂ % 4 = 1 := by omega
    rw [← mix_pow_dvd_sq_sub_one h3 k, ← ng_pow_dvd_sq_sub_one h1' k]
    exact hsq _

theorem t5_two_part_mix_of_setup {G : Type} [Group G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hmod : q₁ % 4 ≠ q₂ % 4) :
    ∀ k : ℕ, 2 ^ k ∣ q₁ + 1 ↔ 2 ^ k ∣ q₂ - 1 :=
  t5_two_part_mix hSet.odd₁ hSet.odd₂ (t5_two_part_sq hSet) hmod

end CFSG.GH74.GLS.Stage4.Rest
