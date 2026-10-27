module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

theorem isPGroup_zpowers {G : Type*} [Group G] {m : G} {k : ℕ} (h : m ^ 2 ^ k = 1) :
    IsPGroup 2 (zpowers m) :=
  IsPGroup.of_card_dvd_pow (n := k) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one h)

theorem eq_of_odd_mul_eq {a b i d : ℕ} (ha : ∃ s : ℕ, a = 2 ^ s) (hb : ∃ s : ℕ, b = 2 ^ s)
    (hi : Odd i) (hd : Odd d) (h : a * i = b * d) : a = b := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  have hcd : Nat.Coprime (2 ^ s) d := Nat.Coprime.pow_left s (Nat.coprime_two_left.2 hd)
  have hci : Nat.Coprime (2 ^ t) i := Nat.Coprime.pow_left t (Nat.coprime_two_left.2 hi)
  have h1 : 2 ^ s ∣ 2 ^ t := hcd.dvd_of_dvd_mul_right ⟨i, h.symm⟩
  have h2 : 2 ^ t ∣ 2 ^ s := hci.dvd_of_dvd_mul_right ⟨d, h⟩
  exact Nat.dvd_antisymm h1 h2

theorem exists_two_part {G : Type*} [Group G] [Finite G] (d : G) :
    ∃ j : ℕ, (∃ k : ℕ, (d ^ j) ^ 2 ^ k = 1) ∧ ∃ o : ℕ, Odd o ∧ (d * (d ^ j)⁻¹) ^ o = 1 := by
  obtain ⟨s, o, ho, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  have hdn : d ^ (2 ^ s * o) = 1 := by rw [← hn]; exact pow_orderOf_eq_one d
  by_cases hs : s = 0
  · subst hs
    refine ⟨0, ⟨0, by simp⟩, o, ho, ?_⟩
    simpa using hdn
  have hs1 : 1 < 2 ^ s := Nat.one_lt_two_pow hs
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.Coprime.pow_right s (Nat.coprime_two_right.2 ho)) hs1
  obtain ⟨t, ht⟩ : ∃ t : ℕ, 2 ^ s * t + 1 = o * u :=
    ⟨o * u / 2 ^ s, by have := Nat.div_add_mod (o * u) (2 ^ s); rw [hu] at this; exact this⟩
  have hj : o * u = 1 + 2 ^ s * t := by omega
  refine ⟨o * u, ⟨s, ?_⟩, o, ho, ?_⟩
  · rw [← pow_mul, show o * u * 2 ^ s = (2 ^ s * o) * u by ring, pow_mul, hdn, one_pow]
  · have h1 : d * (d ^ (o * u))⁻¹ = d ^ ((1 : ℤ) - ((o * u : ℕ) : ℤ)) := by
      rw [zpow_sub, zpow_one, zpow_natCast]
    rw [h1, ← zpow_natCast, ← zpow_mul]
    have h2 : (((1 : ℤ) - ((o * u : ℕ) : ℤ)) * (o : ℤ)) = -((2 ^ s * o : ℕ) : ℤ) * (t : ℤ) := by
      rw [hj]
      push_cast
      ring
    rw [h2, zpow_mul, zpow_neg]
    simp only [zpow_natCast, hdn, inv_one, one_pow]

theorem exists_pow_seven_part {G : Type*} [Group G] [Finite G] (c : G) :
    ∃ k : ℕ, k % 7 = 1 ∧ ∃ a : ℕ, (c ^ k) ^ 7 ^ a = 1 := by
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 7 (by norm_num)
  have hcn : c ^ (7 ^ e * m) = 1 := by rw [← hn]; exact pow_orderOf_eq_one c
  have hcop : Nat.Coprime m 7 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).2 hm).symm
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  refine ⟨m * s, hs, e, ?_⟩
  rw [← pow_mul, show m * s * 7 ^ e = (7 ^ e * m) * s by ring, pow_mul, hcn, one_pow]

end CFSG.EvenSporadicStandard.ReeStd
