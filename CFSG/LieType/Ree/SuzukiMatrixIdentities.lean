module

public import CFSG.LieType.Ree.SuzukiFrobeniusExponents
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix

variable (a : ℕ) {K : Type} [Field K]

theorem suzuki_frob_data [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (2 : K) = 0 ∧ (∀ x y : K, (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1)) ∧
      ∀ x : K, (x ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = x ^ 2 := by
  obtain ⟨hchar, -, hθθ, -⟩ := suzuki_frobenius_exponents a K hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨by exact_mod_cast CharP.cast_eq_zero K 2, fun x y => add_pow_char_pow x y 2 (a + 1), hθθ⟩

theorem suzukiS_mul [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v c d : K) :
    suzukiS a u v * suzukiS a c d = suzukiS a (u + c) (v + d + u ^ 2 ^ (a + 1) * c) := by
  obtain ⟨h2, hadd, hθθ⟩ := suzuki_frob_data a hK
  have hF2 : (v + d + u ^ 2 ^ (a + 1) * c) ^ 2 ^ (a + 1) =
      v ^ 2 ^ (a + 1) + d ^ 2 ^ (a + 1) + u ^ 2 * c ^ 2 ^ (a + 1) := by
    rw [hadd, hadd, mul_pow, hθθ]
  have hN : suzukiN a (u + c) (v + d + u ^ 2 ^ (a + 1) * c) =
      suzukiN a u v + (u ^ (2 ^ (a + 1) + 1) + v) * c + u * d + suzukiN a c d := by
    rw [suzukiN, suzukiN, suzukiN, hF2, pow_add (u + c), hadd]
    linear_combination (u ^ 2 ^ (a + 1) * u * c + u ^ 2 ^ (a + 1) * c ^ 2 +
      c ^ 2 ^ (a + 1) * u ^ 2 + c ^ 2 ^ (a + 1) * c * u) * h2
  have h31 : (u + c) ^ (2 ^ (a + 1) + 1) + (v + d + u ^ 2 ^ (a + 1) * c) =
      u ^ (2 ^ (a + 1) + 1) + v + u * c ^ 2 ^ (a + 1) + (c ^ (2 ^ (a + 1) + 1) + d) := by
    rw [pow_succ, hadd]
    linear_combination u ^ 2 ^ (a + 1) * c * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiS, Matrix.mul_apply, Fin.sum_univ_four, hadd, hN, h31]
  ring

theorem suzuki_unipotent_product [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ u v c d : K,
      suzukiS a u v * suzukiS a c d = suzukiS a (u + c) (v + d + u ^ 2 ^ (a + 1) * c)) ∧
    (∀ u v : K, (suzukiS a u v)⁻¹ = suzukiS a u (v + u ^ (2 ^ (a + 1) + 1))) ∧
    (∀ u v : K, suzukiS a u v ^ 2 = suzukiS a 0 (u ^ (2 ^ (a + 1) + 1))) ∧
    (∀ u v c d : K, (suzukiS a u v)⁻¹ * (suzukiS a c d)⁻¹ * suzukiS a u v * suzukiS a c d =
      suzukiS a 0 (u ^ 2 ^ (a + 1) * c + c ^ 2 ^ (a + 1) * u)) ∧
    suzukiS a (0 : K) 0 = 1 ∧
    (∀ u v c d : K, suzukiS a u v = suzukiS a c d ↔ u = c ∧ v = d) := by
  obtain ⟨h2, hadd, hθθ⟩ := suzuki_frob_data a hK
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hS0 : suzukiS a (0 : K) 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN]
  have hmul := suzukiS_mul a hK
  have hinv : ∀ u v : K, suzukiS a u v * suzukiS a u (v + u ^ (2 ^ (a + 1) + 1)) = 1 := by
    intro u v
    rw [hmul, ← hS0]
    congr 1
    · linear_combination u * h2
    · linear_combination (v + u ^ (2 ^ (a + 1) + 1)) * h2
  have hinv' : ∀ u v : K, (suzukiS a u v)⁻¹ = suzukiS a u (v + u ^ (2 ^ (a + 1) + 1)) :=
    fun u v => Matrix.inv_eq_right_inv (hinv u v)
  refine ⟨hmul, hinv', fun u v => ?_, fun u v c d => ?_, hS0, fun u v c d => ⟨fun h => ?_, ?_⟩⟩
  · rw [sq, hmul]
    congr 1
    · linear_combination u * h2
    · rw [pow_succ]
      linear_combination v * h2
  · rw [hinv', hinv', hmul, hmul, hmul]
    congr 1
    · linear_combination (u + c) * h2
    · simp only [hadd]
      linear_combination (v + d + u ^ (2 ^ (a + 1) + 1) + c ^ (2 ^ (a + 1) + 1) +
        u ^ 2 ^ (a + 1) * c) * h2
  · have h10 := congrFun (congrFun h 1) 0
    have h20 := congrFun (congrFun h 2) 0
    simp [suzukiS] at h10 h20
    exact ⟨h10, h20⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end CFSG.LieType.Ree
