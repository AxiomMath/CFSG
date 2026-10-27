module

public import CFSG.LieType.Ree.SuzukiMatrixIdentities
public import CFSG.LieType.Ree.SuzukiNorm

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint

variable (a : ℕ) {K : Type} [Field K]

theorem suzukiN_pow_succ [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) :
    suzukiN a u v ^ (2 ^ (a + 1) + 1) = v ^ (2 ^ (a + 1) + 2) +
      u * v * suzukiN a u v ^ 2 ^ (a + 1) + u ^ 2 ^ (a + 1) * suzukiN a u v ^ 2 := by
  obtain ⟨h2, hadd, hθθ⟩ := suzuki_frob_data a hK
  have ht : suzukiN a u v = u ^ 2 ^ (a + 1) * u ^ 2 + u * v + v ^ 2 ^ (a + 1) := by
    rw [suzukiN, pow_add]
  have htθ : suzukiN a u v ^ 2 ^ (a + 1) =
      (u ^ 2 ^ (a + 1)) ^ 2 * u ^ 2 + u ^ 2 ^ (a + 1) * v ^ 2 ^ (a + 1) + v ^ 2 := by
    rw [ht, hadd, hadd, mul_pow, mul_pow, hθθ, hθθ, ← pow_mul, ← pow_mul, mul_comm 2,
      pow_mul]
    ring
  rw [pow_succ, htθ, ht, pow_add v]
  linear_combination (-(u ^ 2 ^ (a + 1)) ^ 2 * u ^ 3 * v -
    u ^ 2 ^ (a + 1) * u * v * v ^ 2 ^ (a + 1)) * h2

theorem suzuki_norm_inversion [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ u v : K, suzukiN a u v ^ (2 ^ (a + 1) + 1) = v ^ (2 ^ (a + 1) + 2) +
      u * v * suzukiN a u v ^ 2 ^ (a + 1) + u ^ 2 ^ (a + 1) * suzukiN a u v ^ 2) ∧
    ∀ u v : K, (u, v) ≠ (0, 0) →
      suzukiN a (v / suzukiN a u v) (u / suzukiN a u v) = 1 / suzukiN a u v := by
  refine ⟨suzukiN_pow_succ a hK, fun u v huv => ?_⟩
  have ht : suzukiN a u v ≠ 0 := fun h =>
    huv (Prod.ext ((suzuki_norm_nonzero a K hK u v).1 h).1 ((suzuki_norm_nonzero a K hK u v).1 h).2)
  have hid := suzukiN_pow_succ a hK u v
  set t := suzukiN a u v with htdef
  rw [suzukiN, div_eq_mul_inv, div_eq_mul_inv, one_div]
  have hts : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  refine mul_left_cancel₀ (pow_ne_zero (2 ^ (a + 1) + 2) ht) ?_
  have e1 : (t * t⁻¹) ^ (2 ^ (a + 1) + 2) = 1 := by rw [hts, one_pow]
  have e2 : (t * t⁻¹) ^ 2 = 1 := by rw [hts, one_pow]
  have e3 : (t * t⁻¹) ^ 2 ^ (a + 1) = 1 := by rw [hts, one_pow]
  linear_combination v ^ (2 ^ (a + 1) + 2) * e1 + u * v * t ^ 2 ^ (a + 1) * e2 +
    u ^ 2 ^ (a + 1) * t ^ 2 * e3 - hid - t ^ (2 ^ (a + 1) + 1) * hts

end CFSG.LieType.Ree
