module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult

theorem not_sq_dvd_lyOrder {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) :
    ¬ p ^ 2 ∣ 51765179004000000 := by
  have hfac : (51765179004000000 : ℕ) = (2 ^ 8 * 3 ^ 7 * 5 ^ 6) * 5917373 := by norm_num
  have hc2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 h2
  have hc3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 h3
  have hc5 : Nat.Coprime p 5 := (Nat.coprime_primes hp Nat.prime_five).2 h5
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 8 * 3 ^ 7 * 5 ^ 6) :=
    Nat.Coprime.pow_left 2
      (((hc2.pow_right 8).mul_right (hc3.pow_right 7)).mul_right (hc5.pow_right 6))
  rw [hfac]
  intro hd
  have hsq : p ^ 2 ∣ 5917373 := hcop.dvd_of_dvd_mul_left hd
  have hp1 : p ∣ 5917373 := (dvd_pow_self p two_ne_zero).trans hsq
  have hprod : (5917373 : ℕ) = 7 * 11 * 31 * 37 * 67 := by norm_num
  rw [hprod] at hp1 hsq
  rcases (Nat.Prime.dvd_mul hp).1 hp1 with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
          subst this
          norm_num at hsq
        · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
          subst this
          norm_num at hsq
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        subst this
        norm_num at hsq
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
      subst this
      norm_num at hsq
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    subst this
    norm_num at hsq

theorem factorization_two_lyOrder : (51765179004000000 : ℕ).factorization 2 = 8 := by
  have h : (51765179004000000 : ℕ) = 2 ^ 8 * (3 ^ 7 * 5 ^ 6 * 5917373) := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_three_lyOrder : (51765179004000000 : ℕ).factorization 3 = 7 := by
  have h : (51765179004000000 : ℕ) = 3 ^ 7 * (2 ^ 8 * 5 ^ 6 * 5917373) := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_two_cover_alt11 : (39916800 : ℕ).factorization 2 = 8 := by
  have h : (39916800 : ℕ) = 2 ^ 8 * 155925 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_three_cover_mcl : (2694384000 : ℕ).factorization 3 = 7 := by
  have h : (2694384000 : ℕ) = 3 ^ 7 * 1232000 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult
