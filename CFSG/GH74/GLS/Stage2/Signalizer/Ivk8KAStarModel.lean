module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KATwoC

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.ComponentClassification.PSL3Four CFSG.GH74.GLS.Stage2.Signalizer.Odd87

local notation "Perm42" => Equiv.Perm (Fin 42)

structure StarModel : Prop where
  exp : ∀ p k : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p ^ k → x ^ p = 1
  elt : ∀ (i : Fin 4) (p : ℕ), (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p →
    rr i * x = x * rr i → (i = 3 ∧ p = 3 ∧ x ∈ S) ∨ ∃ c ∈ CC i, (x * (c * x * c⁻¹)) ^ p ≠ 1
  c0 : ∀ e ∈ CC 3, orderOf e = 3 → ∃ c ∈ CC 3, c * e * c⁻¹ ≠ e ∧ c * e * c⁻¹ * e ≠ 1

structure PCfgStar (r : Perm42) (p : ℕ) (P : Subgroup Perm42) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  le_R : P ≤ R
  pgroup : IsPGroup p ↥P
  ne_bot : P ≠ ⊥
  comm : ∀ e ∈ P, e * r = r * e
  norm : ∀ s ∈ S, r * s = s * r → s ∈ normalizer (P : Set Perm42)

section Model


theorem star_model_of (F : StarModel) {i : Fin 4} {p : ℕ}
    {P : Subgroup Perm42} (h : PCfgStar (rr i) p P) : i = 3 ∧ p = 3 ∧ Nat.card ↥P = 9 := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨y, hyP, hyo⟩ := exists_orderOf_eq_prime h.prime h.pgroup h.ne_bot
  have hyR := h.le_R hyP
  have hp357 : p = 3 ∨ p = 5 ∨ p = 7 := by
    have hdvd : p ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by
      have := orderOf_dvd_natCard (⟨y, hyR⟩ : ↥R)
      rw [Subgroup.orderOf_mk, hyo, card_R] at this
      norm_num
      exact this
    rcases (Nat.Prime.dvd_mul h.prime).1 hdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.prime).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul h.prime).1 h2 with h3 | h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1
            (h.prime.dvd_of_dvd_pow h3)) h.odd
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1
            (h.prime.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_five).1 h2))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq h.prime (by norm_num)).1 h1))
  have hnorm' : ∀ c ∈ CC i, ∀ x ∈ P, c * x * c⁻¹ ∈ P := by
    intro c hc x hx
    obtain ⟨hcr, hcS⟩ := mem_CC.1 hc
    exact (Subgroup.mem_normalizer_iff.1 (h.norm c hcS hcr) x).1 hx
  have hPexp : ∀ x ∈ P, x ^ p = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h.pgroup) ⟨x, hx⟩
    exact F.exp p k hp357 x (h.le_R hx) (by rwa [Subgroup.orderOf_mk] at hk)
  have helt : ∀ x ∈ P, orderOf x = p → (i = 3 ∧ p = 3 ∧ x ∈ S) := by
    intro x hx hxo
    rcases F.elt i p hp357 x (h.le_R hx) hxo (h.comm x hx).symm with hE | ⟨c, hc, hne⟩
    · exact hE
    · exact absurd (hPexp _ (P.mul_mem hx (hnorm' c hc x hx))) hne
  obtain ⟨hi3, hp3, -⟩ := helt y hyP hyo
  subst hi3
  subst hp3
  have hPC : P ≤ CC 3 := by
    intro x hx
    refine mem_CC.2 ⟨(h.comm x hx).symm, ?_⟩
    by_cases hx1 : x = 1
    · rw [hx1]
      exact S.one_mem
    · refine (helt x hx ?_).2.2
      have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hPexp x hx)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.1 h1) hx1
      · exact h1
  have h72 : Nat.card ↥(CC 3) = 72 := card_C₄
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h.pgroup
  have hdvd : 3 ^ k ∣ 72 := by
    rw [← hk, ← h72]
    exact Subgroup.card_dvd_of_le hPC
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h.ne_bot (Subgroup.eq_bot_of_card_eq P (by simpa using hk))
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hk2 : k ≤ 2 := by
    by_contra hlt
    have h27 : 3 ^ 3 ∣ 72 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at h27
  refine ⟨rfl, rfl, ?_⟩
  interval_cases k
  · exfalso
    have hcard3 : Nat.card ↥P = 3 := by simpa using hk
    obtain ⟨c₀, hc₀, hne1, hne2⟩ := F.c0 y (hPC hyP) hyo
    have hzp : zpowers y = P := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hyP) ?_
      rw [Nat.card_zpowers, hyo, hcard3]
    have hfP : c₀ * y * c₀⁻¹ ∈ zpowers y := hzp ▸ hnorm' c₀ hc₀ y hyP
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hfP
    have hm3 : y ^ m = y ^ (m % 3) := by
      have := zpow_mod_orderOf y m
      rw [hyo] at this
      exact_mod_cast this.symm
    have hy3 : y ^ 3 = 1 := hPexp y hyP
    rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h0 | h0 | h0
    · rw [h0, zpow_zero] at hm3
      rw [hm3] at hm
      have hy1 : y = 1 := by
        calc y = c₀⁻¹ * (c₀ * y * c₀⁻¹) * c₀ := by group
          _ = c₀⁻¹ * 1 * c₀ := by rw [← hm]
          _ = 1 := by group
      rw [hy1, orderOf_one] at hyo
      omega
    · rw [h0, zpow_one] at hm3
      rw [hm3] at hm
      exact hne1 hm.symm
    · rw [h0] at hm3
      rw [hm3] at hm
      apply hne2
      rw [← hm]
      have : (y ^ (2 : ℤ)) * y = y ^ 3 := by group
      rw [this, hy3]
  · simpa using hk

end Model

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
