module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open Polynomial

theorem orderOf_unitOfCoprime_two_pow {f : ℕ} (hf : Odd f) (h : Nat.Coprime (2 ^ f) 5) :
    orderOf (ZMod.unitOfCoprime (2 ^ f) h) = 4 := by
  obtain ⟨k, rfl⟩ := hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h24 : (2 : ZMod 5) ^ 4 = 1 := by decide
  have hcast : ((ZMod.unitOfCoprime (2 ^ (2 * k + 1)) h : (ZMod 5)ˣ) : ZMod 5) =
      (2 : ZMod 5) ^ (2 * k + 1) := by
    rw [ZMod.coe_unitOfCoprime]
    push_cast
    rfl
  have hsq : ((ZMod.unitOfCoprime (2 ^ (2 * k + 1)) h) ^ 2 : (ZMod 5)ˣ) ≠ 1 := by
    intro hu
    have := congrArg (fun u : (ZMod 5)ˣ => (u : ZMod 5)) hu
    simp only [Units.val_pow_eq_pow_val, hcast, Units.val_one] at this
    rw [← pow_mul, show (2 * k + 1) * 2 = 2 + 4 * k by ring, pow_add, pow_mul, h24, one_pow,
      mul_one] at this
    revert this
    decide
  have hfour : ((ZMod.unitOfCoprime (2 ^ (2 * k + 1)) h) ^ 4 : (ZMod 5)ˣ) = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, hcast, Units.val_one]
    rw [← pow_mul, show (2 * k + 1) * 4 = 4 * (2 * k + 1) by ring, pow_mul, h24, one_pow]
  have := orderOf_eq_prime_pow (p := 2) (n := 1)
    (x := ZMod.unitOfCoprime (2 ^ (2 * k + 1)) h) (by simpa using hsq) (by simpa using hfour)
  simpa using this

theorem charpoly_eq_cyclotomic_five {K : Type} [Field K] [Fintype K] {f : ℕ}
    (hf : Odd f) (hK : Fintype.card K = 2 ^ f) (C : Matrix (Fin 4) (Fin 4) K)
    (h5 : C ^ 5 = 1) (h1 : C ≠ 1) : C.charpoly = cyclotomic 5 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : Nat.Coprime 2 5 := by norm_num
  have hdeg : (cyclotomic 5 K).natDegree = 4 := by
    rw [natDegree_cyclotomic, Nat.totient_prime Nat.prime_five]
  have hirr : Irreducible (cyclotomic 5 K) :=
    irreducible_of_dvd_cyclotomic_of_natDegree hK hn dvd_rfl
      (by rw [hdeg, orderOf_unitOfCoprime_two_pow hf (hn.pow_left f)])
  have hmdvd : minpoly K C ∣ cyclotomic 5 K * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [h5]
  have hmχ : minpoly K C ∣ C.charpoly := Matrix.minpoly_dvd_charpoly C
  by_cases hΦ : cyclotomic 5 K ∣ minpoly K C
  · refine (eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic 5 K) (Matrix.charpoly_monic C)
      (hΦ.trans hmχ) ?_)
    rw [Matrix.charpoly_natDegree_eq_dim, hdeg]
    simp
  · exfalso
    have hcop : IsCoprime (cyclotomic 5 K) (minpoly K C) :=
      (Irreducible.coprime_iff_not_dvd hirr).mpr hΦ
    obtain ⟨c, hc⟩ := hcop.symm.dvd_of_dvd_mul_left hmdvd
    have h0 : Polynomial.aeval C (X - 1 : K[X]) = 0 := by
      rw [hc, map_mul, minpoly.aeval, zero_mul]
    simp only [map_sub, aeval_X, map_one] at h0
    exact h1 (sub_eq_zero.mp h0)

end CFSG.CGT.PushingUpLit.SolKNA
