module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemmaP
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup

theorem card_quotient_modEq {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {e : G} (he : e * e = 1) (N : Subgroup G) (m : ℕ)
    (hN : Nat.card N = 3072) (hC : Nat.card (centralizer ({e} : Set G)) = 190080)
    (hm : Nat.card {y : N // IsConj e (y : G)} = m) :
    Nat.card G = Nat.card (G ⧸ N) * 3072 ∧ Nat.card (G ⧸ N) * 3072 = Nat.card G ∧
      Nat.card (G ⧸ N) ≡ Nat.card (MulAction.fixedBy (G ⧸ N) e) [MOD 4] ∧
      Nat.card (MulAction.fixedBy (G ⧸ N) e) * 3072 = 190080 * m := by
  have h1 : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h2 := card_fixedBy_quotient_mul N e
  rw [hN, hC, hm] at h2
  rw [hN] at h1
  exact ⟨h1, h1.symm, card_modEq_fixedBy_four hna he, h2⟩

theorem factorization_two_mul {X : ℕ} (hX : X % 4 = 2) : (X * 3072).factorization 2 = 11 := by
  obtain ⟨Y, hY⟩ : ∃ Y, X = 2 * (2 * Y + 1) := ⟨X / 4, by omega⟩
  have hX0 : X ≠ 0 := by omega
  rw [Nat.factorization_def _ Nat.prime_two]
  have h : X * 3072 = 2 ^ 11 * (3 * (2 * Y + 1)) := by rw [hY]; ring
  rw [h, padicValNat.mul (by norm_num) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega)]

theorem factorization_two_mul_odd {X : ℕ} (hX : X % 2 = 1) : (X * 3072).factorization 2 = 10 := by
  obtain ⟨Y, hY⟩ : ∃ Y, X = 2 * Y + 1 := ⟨X / 2, by omega⟩
  rw [Nat.factorization_def _ Nat.prime_two]
  have h : X * 3072 = 2 ^ 10 * (3 * (2 * Y + 1)) := by rw [hY]; ring
  rw [h, padicValNat.mul (by norm_num) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega)]

theorem factorization_eq_eleven {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {e : G} (he : e * e = 1) (N : Subgroup G)
    (hN : Nat.card N = 3072) (hC : Nat.card (centralizer ({e} : Set G)) = 190080)
    (hm : Nat.card {y : N // IsConj e (y : G)} = 80) : (Nat.card G).factorization 2 = 11 := by
  obtain ⟨h1, -, h3, h4⟩ := card_quotient_modEq hna he N 80 hN hC hm
  have h5 : Nat.card (MulAction.fixedBy (G ⧸ N) e) = 4950 := by omega
  rw [h5] at h3
  have h6 : Nat.card (G ⧸ N) % 4 = 2 := by
    have := h3
    unfold Nat.ModEq at this
    omega
  rw [h1]
  exact factorization_two_mul h6

theorem factorization_eq_ten {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {e : G} (he : e * e = 1) (N : Subgroup G)
    (hN : Nat.card N = 3072) (hC : Nat.card (centralizer ({e} : Set G)) = 190080)
    (hm : Nat.card {y : N // IsConj e (y : G)} = 200) : (Nat.card G).factorization 2 = 10 := by
  obtain ⟨h1, -, h3, h4⟩ := card_quotient_modEq hna he N 200 hN hC hm
  have h5 : Nat.card (MulAction.fixedBy (G ⧸ N) e) = 12375 := by omega
  rw [h5] at h3
  have h6 : Nat.card (G ⧸ N) % 2 = 1 := by
    have := h3
    unfold Nat.ModEq at this
    omega
  rw [h1]
  exact factorization_two_mul_odd h6

end CFSG.EvenSporadicStandard.M12Std.Yosh
