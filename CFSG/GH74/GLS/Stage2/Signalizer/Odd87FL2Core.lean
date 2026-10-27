module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Cent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Char

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

section Core

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem fl2_barcore (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K) (hα : α * α = 1)
    (hα1 : α ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Y : Subgroup K) (hY : IsPGroup p ↥Y)
    (hY1 : Y ≠ ⊥) (hYα : ∀ y ∈ Y, α y ∈ Y)
    (hYc : Subgroup.closure {y : K | ∃ x ∈ Y, y = x * (α x)⁻¹} = Y) (C : Subgroup K)
    (hCfix : ∀ c ∈ C, α c = c) (hCN : ∀ c ∈ C, c ∈ normalizer (Y : Set K)) {c : ℕ}
    (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hfix : Nat.card ↥(fixedSubgroup K α) ≤ c * Nat.card ↥C) :
    (p ∣ Nat.card F ∧ Nat.card ↥Y = Nat.card F ∧ c = 2 ∧
        ∀ m ∈ normalizer (Y : Set K), ∃ y ∈ Y, ∃ c' ∈ C, m = y * c') ∨
      (¬ p ∣ Nat.card F ∧ c = 2 ∧ Nat.card F = 5 ∧ Nat.card ↥Y = 3 ∧ p = 3 ∧
        ∀ m ∈ normalizer (Y : Set K), ∃ y ∈ Y, ∃ c' ∈ C, m = y * c') := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq := fixedSubgroup_card_ge hF e α hα hα1
  have hodd := hF.1
  have hq3 := hF.2
  have hCle : C ≤ fixedSubgroup K α := fun x hx => hCfix x hx
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  have hY1' : 1 < Nat.card ↥Y := (Subgroup.one_lt_card_iff_ne_bot Y).mpr hY1
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    rw [this, pow_zero] at hk
    omega
  have hpY : p ≤ Nat.card ↥Y := by
    rw [hk]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk1
  by_cases hpF : p ∣ Nat.card F
  ·
    left
    refine ⟨hpF, ?_⟩
    rcases fixedSubgroup_coprime_or_pgl hF e α hα hα1 with hcop | ⟨F₀, _, _, h3, hq₀, ⟨eG⟩⟩
    · have hpchar : ringChar F = p := by
        have : Fintype F := Fintype.ofFinite F
        obtain ⟨n, hpr, hn⟩ := FiniteField.card F (ringChar F)
        have : p ∣ ringChar F ^ (n : ℕ) := hn ▸ (Nat.card_eq_fintype_card (α := F) ▸ hpF)
        exact ((Nat.prime_dvd_prime_iff_eq hp hpr).mp (hp.dvd_of_dvd_pow this)).symm
      have hpC : ¬ p ∣ Nat.card ↥C := by
        intro hdvd
        apply hcop
        rw [hpchar]
        exact hdvd.trans (Subgroup.card_dvd_of_le hCle)
      have hCbig : (Nat.card F - 1) / 2 ≤ Nat.card ↥C := by
        have : Nat.card F - 1 ≤ 2 * Nat.card ↥C := by nlinarith
        omega
      obtain ⟨hYq, hCq, hNorm⟩ := fl2_char_free hF e hp hpF Y hY hY1 C hCN hpC hCbig
      refine ⟨hYq, ?_, hNorm⟩
      rcases (by omega : c = 1 ∨ c = 2) with h | h
      · exfalso
        subst h
        have : Nat.card F - 1 ≤ Nat.card ↥C := by nlinarith
        obtain ⟨m, hm⟩ := hodd
        omega
      · exact h
    · exfalso
      have hodd₀ : Odd (Nat.card F₀) := by
        by_contra hev
        have h1 : Even (Nat.card F₀) := Nat.not_odd_iff_even.mp hev
        have h2 : Even (Nat.card F₀ * Nat.card F₀) := h1.mul_right _
        rw [hq₀] at h2
        exact (Nat.not_even_iff_odd.mpr hodd) h2
      have hidx : C.relIndex (fixedSubgroup K α) ≤ 2 := by
        have h1 := Subgroup.relIndex_mul_card C (fixedSubgroup K α)
        rw [inf_eq_left.mpr hCle] at h1
        have hCpos : 0 < Nat.card ↥C := Nat.card_pos
        have h2 : C.relIndex (fixedSubgroup K α) * Nat.card C ≤ 2 * Nat.card C := by
          calc _ = Nat.card (fixedSubgroup K α) := h1
            _ ≤ c * Nat.card C := hfix
            _ ≤ 2 * Nat.card C := Nat.mul_le_mul_right _ hc2
        exact Nat.le_of_mul_le_mul_right h2 hCpos
      exact fl2_char_pgl hF e hp hpF Y hY hY1 (fixedSubgroup K α) h3 hodd₀ eG C hidx hCN
  ·
    right
    obtain ⟨hcross, hcrossN⟩ := fl2_cross hF e α hp hp2 hpF Y hY hY1 hYα hYc C hCfix hCN
    refine ⟨hpF, ?_⟩
    have hy3 : 3 ≤ Nat.card ↥Y := by
      have : 3 ≤ p := by have := hp.two_le; omega
      omega
    have hA : (Nat.card F - 1) * Nat.card ↥Y ≤ 2 * (Nat.card F + 1) := by
      calc (Nat.card F - 1) * Nat.card ↥Y ≤ (c * Nat.card ↥C) * Nat.card ↥Y :=
            Nat.mul_le_mul_right _ (le_trans hq hfix)
        _ = c * (Nat.card ↥C * Nat.card ↥Y) := by ring
        _ ≤ 2 * (Nat.card F + 1) := Nat.mul_le_mul hc2 hcross
    have hB : 3 * (Nat.card F - 1) ≤ (Nat.card F - 1) * Nat.card ↥Y := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ hy3
    obtain ⟨m, hm⟩ := hodd
    have hq5 : Nat.card F = 5 := by omega
    rw [hq5] at hA
    have hy : Nat.card ↥Y = 3 := by omega
    have hc : c = 2 := by
      rcases (by omega : c = 1 ∨ c = 2) with h | h
      · exfalso
        subst h
        have h1 : Nat.card F - 1 ≤ Nat.card ↥C := by simpa using le_trans hq hfix
        have h2 : (Nat.card F - 1) * Nat.card ↥Y ≤ Nat.card ↥C * Nat.card ↥Y := Nat.mul_le_mul_right _ h1
        rw [hq5] at h2 hcross
        have h3 := le_trans h2 hcross
        rw [hy] at h3
        omega
      · exact h
    have hCcard : Nat.card ↥C * Nat.card ↥Y = Nat.card F + 1 := by
      have h1 : Nat.card F - 1 ≤ 2 * Nat.card ↥C := by
        have := le_trans hq hfix
        rwa [hc] at this
      rw [hq5, hy] at hcross ⊢
      omega
    refine ⟨hc, hq5, hy, ?_, hcrossN hCcard⟩
    have hpd : p ∣ Nat.card ↥Y := by
      rw [hk]; exact dvd_pow_self p (by omega)
    rw [hy] at hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
