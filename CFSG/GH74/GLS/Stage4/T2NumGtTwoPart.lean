module

public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG CFSG.GH74.GLS.Stage4 CFSG.Assembly.LowTwoRank

theorem ng_pow_dvd_sq_sub_one {q : ℕ} (hq : q % 4 = 1) (k : ℕ) :
    2 ^ (k + 1) ∣ q ^ 2 - 1 ↔ 2 ^ k ∣ q - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, q = 4 * j + 1 := ⟨q / 4, by omega⟩
  have h1 : (4 * j + 1) ^ 2 - 1 = 2 * (4 * j) * (2 * j + 1) := by
    have : (4 * j + 1) ^ 2 = 2 * (4 * j) * (2 * j + 1) + 1 := by ring
    omega
  have h2 : 4 * j + 1 - 1 = 4 * j := by omega
  rw [h1, h2]
  have hcop : Nat.Coprime (2 ^ (k + 1)) (2 * j + 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact odd_two_mul_add_one j
  rw [Nat.Coprime.dvd_mul_right hcop, pow_succ, mul_comm 2 (4 * j)]
  rw [mul_comm (2 ^ k) 2, mul_comm (4 * j) 2]
  exact Nat.mul_dvd_mul_iff_left (by norm_num)

theorem ng_card_statedSL {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem t5_two_part_sq {G : Type} [Group G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) :
    ∀ k : ℕ, 2 ^ k ∣ q₁ ^ 2 - 1 ↔ 2 ^ k ∣ q₂ ^ 2 - 1 := by
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨p, f, F, iF, fF, hp, hp2, hL, hcF, hs₁, hs₂⟩ := hSet.model
  have h1 := ng_card_statedSL (F := F₁)
  have h2 := ng_card_statedSL (F := F₂)
  rw [hSet.card₁] at h1
  rw [hSet.card₂] at h2
  rw [h1] at hs₁
  rw [h2] at hs₂
  have hs : (q₁ * (q₁ ^ 2 - 1)).factorization 2 = (q₂ * (q₂ ^ 2 - 1)).factorization 2 := hs₁.trans hs₂.symm
  have hq₁0 : q₁ ≠ 0 := by have := hSet.five; omega
  have hq₂0 : q₂ ≠ 0 := by have := hSet.odd₂; rcases this with ⟨k, hk⟩; omega
  have hsq₁ : q₁ ^ 2 - 1 ≠ 0 := by
    have h5 := hSet.five
    have : 1 < q₁ ^ 2 := by nlinarith
    omega
  have hsq₂ : q₂ ^ 2 - 1 ≠ 0 := by
    have : 3 ≤ q₂ := by
      have h1q : 1 < Nat.card F₂ := Finite.one_lt_card
      rw [hSet.card₂] at h1q
      rcases hSet.odd₂ with ⟨k, hk⟩
      omega
    have : 1 < q₂ ^ 2 := by nlinarith
    omega
  have hodd₁ : Nat.factorization q₁ 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    rcases hSet.odd₁ with ⟨k, hk⟩; omega
  have hodd₂ : Nat.factorization q₂ 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    rcases hSet.odd₂ with ⟨k, hk⟩; omega
  rw [Nat.factorization_mul hq₁0 hsq₁, Nat.factorization_mul hq₂0 hsq₂] at hs
  simp only [Finsupp.add_apply, hodd₁, hodd₂, zero_add] at hs
  intro k
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hsq₁,
    Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hsq₂, hs]

theorem t5_two_part {G : Type} [Group G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hmod : q₁ % 4 = q₂ % 4) :
    ∀ k : ℕ, 2 ^ k ∣ q₁ - 1 ↔ 2 ^ k ∣ q₂ - 1 := by
  have hv := t5_two_part_sq hSet
  have hq₁4 : q₁ % 4 = 1 ∨ q₁ % 4 = 3 := by rcases hSet.odd₁ with ⟨k, hk⟩; omega
  rcases hq₁4 with h1 | h3
  · have h1' : q₂ % 4 = 1 := by omega
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [← ng_pow_dvd_sq_sub_one h1, ← ng_pow_dvd_sq_sub_one h1']
      exact hv _
  · have h3' : q₂ % 4 = 3 := by omega
    intro k
    have key : ∀ q : ℕ, q % 4 = 3 → (2 ^ k ∣ q - 1 ↔ k ≤ 1) := by
      intro q hq
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
    rw [key q₁ h3, key q₂ h3']

end CFSG.GH74.GLS.Stage4.Rest
