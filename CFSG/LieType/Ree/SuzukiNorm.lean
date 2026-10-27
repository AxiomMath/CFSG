module

public import CFSG.LieType.Ree.SuzukiFrobeniusExponents
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint

theorem suzuki_norm_nonzero (a : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) : suzukiN a u v = 0 ↔ u = 0 ∧ v = 0 := by
  obtain ⟨hchar, -, hθθ, -⟩ := suzuki_frobenius_exponents a K hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  constructor
  · intro hN
    by_cases hu : u = 0
    · subst hu
      refine ⟨rfl, ?_⟩
      rw [suzukiN, zero_pow (by positivity), zero_mul, zero_add, zero_add] at hN
      exact pow_eq_zero_iff hθ0 |>.1 hN
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hadd : ∀ x y : K, (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1) :=
        fun x y => add_pow_char_pow x y 2 (a + 1)
      set t := v / u ^ (2 ^ (a + 1) + 1) with ht
      have hu' : u ^ (2 ^ (a + 1) + 1) ≠ 0 := pow_ne_zero _ hu
      have hv : v = u ^ (2 ^ (a + 1) + 1) * t := by
        rw [ht, mul_div_cancel₀ _ hu']
      have huu : u ^ (2 ^ (a + 1) * 2 ^ (a + 1)) = u ^ 2 := by rw [pow_mul, hθθ]
      have e1 : (u ^ (2 ^ (a + 1) + 1) * t) ^ 2 ^ (a + 1) =
          u ^ (2 ^ (a + 1) + 2) * t ^ 2 ^ (a + 1) := by
        rw [mul_pow, ← pow_mul, add_mul, one_mul, pow_add, huu]
        ring
      have hkey : suzukiN a u v = u ^ (2 ^ (a + 1) + 2) * (1 + t + t ^ 2 ^ (a + 1)) := by
        rw [suzukiN, hv, e1]
        ring
      rw [hkey] at hN
      have h3 : 1 + t + t ^ 2 ^ (a + 1) = 0 :=
        (mul_eq_zero.1 hN).resolve_left (pow_ne_zero _ hu)
      have htθ : t ^ 2 ^ (a + 1) = t + 1 := by linear_combination h3 - h2 * (t + 1)
      have htt : t ^ 2 = t := by
        rw [← hθθ t, htθ, hadd, htθ, one_pow]
        linear_combination h2
      have h01 : t = 0 ∨ t = 1 := by
        have : t * (t - 1) = 0 := by linear_combination htt
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.1 h)
      rcases h01 with h0 | h1
      · rw [h0, zero_pow hθ0, add_zero, add_zero] at h3
        exact one_ne_zero h3
      · rw [h1, one_pow] at h3
        have : (1 : K) = 0 := by linear_combination h3 - h2
        exact one_ne_zero this
  · rintro ⟨rfl, rfl⟩
    rw [suzukiN, zero_pow (by positivity), zero_pow hθ0, mul_zero, add_zero, add_zero]

end CFSG.LieType.Ree
