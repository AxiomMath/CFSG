module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux

theorem charP_two_of_even_natCard (K : Type) [Field K] [Finite K] (h : Even (Nat.card K)) :
    CharP K 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard] at h
  have h2 : 2 ∣ ringChar K ^ (n : ℕ) := even_iff_two_dvd.1 h
  have h3 : 2 ∣ ringChar K := Nat.prime_two.dvd_of_dvd_pow h2
  have h4 : ringChar K = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h3).symm
  exact ringChar.eq_iff.1 h4

theorem ringChar_ne_three_of_dvd_add_one (K : Type) [Field K] [Finite K]
    (h : 3 ∣ Nat.card K + 1) : ringChar K ≠ 3 := by
  classical
  intro h3
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard, h3] at h
  have h1 : 3 ∣ 3 ^ (n : ℕ) := dvd_pow_self 3 n.ne_zero
  omega

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux
