module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.AGLEmbedding

theorem zmod_cast_pred {p : ℕ} (hp : 1 ≤ p) : ((p - 1 : ℕ) : ZMod p) = -1 := by
  rw [Nat.cast_sub hp, ZMod.natCast_self]; simp

theorem zmod_cast_sq_pred {p : ℕ} (hp : 1 ≤ p) : ((p ^ 2 - 1 : ℕ) : ZMod p) = -1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hp), Nat.cast_pow, ZMod.natCast_self]; simp

theorem false_of_zmod_eq_zero {p k : ℕ} (hk : 0 < k) (hkp : k < p) (h : (k : ZMod p) = 0) :
    False := by
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd hk h) (by omega)

theorem false_of_arith_trans {p c₁ c₂ : ℕ} (hp : p.Prime) (h₁ : c₁ = 0 ∨ c₁ = p ^ 2 - 1)
    (h₂ : c₂ = 0 ∨ c₂ = p ^ 2 - 1) (h₁' : c₁ ≠ p ^ 2 - 1) (h₂' : c₂ ≠ p ^ 2 - 1)
    (hdvd : p ∣ c₁ + (p - 1) * (1 + c₂)) : False := by
  have hc₁ : c₁ = 0 := h₁.resolve_right h₁'
  have hc₂ : c₂ = 0 := h₂.resolve_right h₂'
  subst hc₁ hc₂
  have : p ∣ p - 1 := by simpa using hdvd
  have h2 := hp.two_le
  have h1 := Nat.le_of_dvd (by omega) this
  omega

theorem false_of_arith_lin {p c₁ c₂ : ℕ} (h5 : 5 ≤ p)
    (h₁ : c₁ = 0 ∨ c₁ = p ^ 2 - 1 ∨ 2 * c₁ = p ^ 2 - 1)
    (h₂ : c₂ = 0 ∨ c₂ = p ^ 2 - 1 ∨ 2 * c₂ = p ^ 2 - 1) (h₁' : c₁ ≠ p ^ 2 - 1)
    (h₂' : c₂ ≠ p ^ 2 - 1) (hdvd : p ∣ c₁ + (p - 1) * (1 + c₂)) : False := by
  have hp1 : 1 ≤ p := by omega
  have hX : ((c₁ + (p - 1) * (1 + c₂) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  push_cast [Nat.cast_sub hp1] at hX
  rw [ZMod.natCast_self] at hX
  have hsq : ((p ^ 2 - 1 : ℕ) : ZMod p) = -1 := zmod_cast_sq_pred hp1
  rcases h₁ with h₁ | h₁ | h₁
  · rcases h₂ with h₂ | h₂ | h₂
    · subst h₁ h₂
      exact false_of_zmod_eq_zero (p := p) (k := 1) (by norm_num) (by omega)
        (by push_cast at hX ⊢; linear_combination -hX)
    · exact h₂' h₂
    · subst h₁
      have h3 : ((2 * c₂ : ℕ) : ZMod p) = -1 := by rw [h₂, hsq]
      push_cast at h3
      exact false_of_zmod_eq_zero (p := p) (k := 1) (by norm_num) (by omega)
        (by push_cast at hX ⊢; linear_combination -2 * hX - h3)
  · exact h₁' h₁
  · have h3 : ((2 * c₁ : ℕ) : ZMod p) = -1 := by rw [h₁, hsq]
    push_cast at h3
    rcases h₂ with h₂ | h₂ | h₂
    · subst h₂
      exact false_of_zmod_eq_zero (p := p) (k := 3) (by norm_num) (by omega)
        (by push_cast at hX ⊢; linear_combination -2 * hX + h3)
    · exact h₂' h₂
    · have h4 : ((2 * c₂ : ℕ) : ZMod p) = -1 := by rw [h₂, hsq]
      push_cast at h4
      exact false_of_zmod_eq_zero (p := p) (k := 2) (by norm_num) (by omega)
        (by push_cast at hX ⊢; linear_combination h3 - h4 - 2 * hX)

theorem arith_alt {p c₁ c₂ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h₁ : c₁ = 0 ∨ c₁ = p ^ 2 - 1 ∨ c₁ = 2 * (p - 1) ∨ c₁ = (p - 1) ^ 2)
    (h₂ : c₂ = 0 ∨ c₂ = p ^ 2 - 1 ∨ c₂ = 2 * (p - 1) ∨ c₂ = (p - 1) ^ 2)
    (h₁' : c₁ ≠ p ^ 2 - 1) (h₂' : c₂ ≠ p ^ 2 - 1) (hdvd : p ∣ c₁ + (p - 1) * (1 + c₂)) :
    (c₂ = 0 ∧ 2 * (p - 1) < c₁) ∨ (p = 3 ∧ c₂ = 0 ∧ c₁ ≠ 0) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp1 : 1 ≤ p := by omega
  have hX : ((c₁ + (p - 1) * (1 + c₂) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  push_cast [Nat.cast_sub hp1] at hX
  rw [ZMod.natCast_self] at hX
  have hpz : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  rcases h₁ with h₁ | h₁ | h₁ | h₁ <;> rcases h₂ with h₂ | h₂ | h₂ | h₂
  all_goals first
    | exact absurd h₁ h₁'
    | exact absurd h₂ h₂'
    | skip
  ·
    subst h₁ h₂
    exact (false_of_zmod_eq_zero (p := p) (k := 1) (by norm_num) (by omega)
      (by push_cast at hX ⊢; linear_combination -hX)).elim
  ·
    subst h₁ h₂
    exact (false_of_zmod_eq_zero (p := p) (k := 1) (by norm_num) (by omega)
      (by push_cast [Nat.cast_sub hp1] at hX ⊢; rw [hpz] at hX; linear_combination hX)).elim
  ·
    subst h₁ h₂
    exact (false_of_zmod_eq_zero (p := p) (k := 2) (by norm_num) (by omega)
      (by push_cast [Nat.cast_sub hp1] at hX ⊢; rw [hpz] at hX; linear_combination -hX)).elim
  ·
    subst h₁ h₂
    right
    refine ⟨?_, rfl, by omega⟩
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast [Nat.cast_sub hp1] at hX ⊢; rw [hpz] at hX; linear_combination -hX
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  ·
    subst h₁ h₂
    exact (false_of_zmod_eq_zero (p := p) (k := 1) (by norm_num) (by omega)
      (by push_cast [Nat.cast_sub hp1] at hX ⊢; rw [hpz] at hX; linear_combination -hX)).elim
  ·
    subst h₁ h₂
    exfalso
    have h4 : ((4 : ℕ) : ZMod p) = 0 := by
      push_cast [Nat.cast_sub hp1] at hX ⊢; rw [hpz] at hX; linear_combination -hX
    rw [ZMod.natCast_eq_zero_iff] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    have h4' : p ∣ 2 ^ 2 := by norm_num; exact h4
    have := hp.dvd_of_dvd_pow h4'
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    exact hp2 this
  ·
    subst h₁ h₂
    by_cases h3 : p = 3
    · right
      exact ⟨h3, rfl, by subst h3; norm_num⟩
    · left
      refine ⟨rfl, ?_⟩
      have h4 : 4 ≤ p := by omega
      have : 2 < p - 1 := by omega
      calc 2 * (p - 1) < (p - 1) * (p - 1) := Nat.mul_lt_mul_of_pos_right this (by omega)
        _ = (p - 1) ^ 2 := (sq _).symm
  ·
    subst h₁ h₂
    exfalso
    exact false_of_zmod_eq_zero (p := p) (k := 2) (by norm_num) (by omega)
      (by push_cast [Nat.cast_sub hp1] at hX ⊢; rw [hpz] at hX; linear_combination hX)
  ·
    subst h₁ h₂
    exfalso
    exact false_of_zmod_eq_zero (p := p) (k := 1) (by norm_num) (by omega)
      (by push_cast [Nat.cast_sub hp1] at hX ⊢; rw [hpz] at hX; linear_combination -hX)

end CFSG.AGLEmbedding
