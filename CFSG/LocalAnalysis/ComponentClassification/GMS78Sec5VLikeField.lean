module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.ComponentClassification.GMS78.VLike

open Polynomial

variable {K : Type*} [Field K] [Fintype K]

section Frob

omit [Fintype K] in
theorem pow_two_pow_mul_eq_self {j : ℕ} {ρ : K} (h : ρ ^ 2 ^ j = ρ) (m : ℕ) :
    ρ ^ 2 ^ (j * m) = ρ := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem eq_zero_or_one_of_pow_two_pow_eq {n j : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 2 ≤ n)
    (hj : Nat.Coprime j n) {ρ : K} (h : ρ ^ 2 ^ j = ρ) : ρ = 0 ∨ ρ = 1 := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hj (by omega)
  have hcard : ∀ t : ℕ, ρ ^ 2 ^ (n * t) = ρ := by
    have h1 : ρ ^ 2 ^ n = ρ := by rw [← hK]; exact FiniteField.pow_card ρ
    exact pow_two_pow_mul_eq_self h1
  have h2 : ρ ^ 2 = ρ := by
    have e : j * m = n * (j * m / n) + 1 := by
      have := Nat.div_add_mod (j * m) n
      omega
    have h3 := pow_two_pow_mul_eq_self h m
    rw [e, pow_succ, pow_mul, hcard] at h3
    exact h3
  have h4 : ρ * (ρ - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h2, sub_self]
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact Or.inl h5
  · exact Or.inr (sub_eq_zero.mp h5)

theorem coprime_a (a : ℕ) : Nat.Coprime a (2 * a + 1) := by
  rw [show 2 * a + 1 = 1 + 2 * a by ring, Nat.coprime_add_mul_right_right]
  exact Nat.coprime_one_right a

theorem coprime_a_succ (a : ℕ) : Nat.Coprime (a + 1) (2 * a + 1) := by
  have h : 2 * a + 1 = (a + 1) + a := by ring
  rw [h, Nat.coprime_self_add_right]
  have := coprime_a a
  rw [Nat.coprime_comm] at this ⊢
  rw [show a + 1 = 1 + 1 * a by ring, Nat.coprime_add_mul_right_right] at *
  exact Nat.coprime_one_right a

end Frob

section Vanish

omit [Fintype K] in
theorem coeffs_eq_zero_of_vanish {a : ℕ} (ha : 1 ≤ a) {α β γ : K} (s : Finset K)
    (hs : 2 ^ (a + 1) < s.card)
    (h : ∀ z ∈ s, α * z ^ 2 ^ (a + 1) + β * z + γ * z ^ 2 ^ a = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  set p : K[X] := C α * X ^ 2 ^ (a + 1) + C β * X + C γ * X ^ 2 ^ a with hp
  have hσ : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hσθ : 2 ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hdeg : p.natDegree ≤ 2 ^ (a + 1) := by
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
    · exact (natDegree_C_mul_X_pow_le _ _)
    · exact (natDegree_C_mul_le β X).trans (natDegree_X_le.trans (by omega))
    · exact (natDegree_C_mul_X_pow_le _ _).trans hσθ.le
  have hp0 : p = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p s (fun z hz => ?_) (by omega)
    simpa [hp] using h z hz
  have c1 := congrArg (fun q : K[X] => q.coeff (2 ^ (a + 1))) hp0
  have c2 := congrArg (fun q : K[X] => q.coeff 1) hp0
  have c3 := congrArg (fun q : K[X] => q.coeff (2 ^ a)) hp0
  have h1 : (2 ^ (a + 1) : ℕ) ≠ 1 := by omega
  have h2 : (1 : ℕ) ≠ 2 ^ a := by omega
  simp only [hp, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_zero] at c1 c2 c3
  refine ⟨?_, ?_, ?_⟩
  · simpa [h1, hσθ.ne'] using c1
  · simpa [h1.symm, h2] using c2
  · simpa [hσθ.ne, h2.symm, show a ≠ 0 by omega] using c3

end Vanish

section Powers

variable [CharP K 2]

omit [Fintype K] in
theorem add_pow_two_pow (x y : K) (m : ℕ) : (x + y) ^ 2 ^ m = x ^ 2 ^ m + y ^ 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact add_pow_char_pow x y 2 m

omit [Fintype K] in
theorem pow_two_pow_injective (m : ℕ) : Function.Injective fun x : K => x ^ 2 ^ m := by
  intro x y hxy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxy' : x ^ 2 ^ m = y ^ 2 ^ m := hxy
  have h : (x - y) ^ 2 ^ m = 0 := by rw [sub_pow_char_pow, hxy', sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_pos (by norm_num) m).ne' |>.mp h)

theorem pow_two_pow_surjective (m : ℕ) : Function.Surjective fun x : K => x ^ 2 ^ m :=
  Finite.injective_iff_surjective.mp (pow_two_pow_injective m)

omit [CharP K 2] in
theorem eq_of_pow_two_pow_mul_eq {a : ℕ} (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {z w : K} (hz : z ≠ 0) (hw : w ≠ 0) (h : z ^ 2 ^ a * w = w ^ 2 ^ a * z) : z = w := by
  have hfix : (z / w) ^ 2 ^ a = z / w := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero _ hw) hw]
    linear_combination h
  rcases eq_zero_or_one_of_pow_two_pow_eq hK (by omega) (coprime_a a) hfix with h0 | h1
  · exact absurd (div_eq_zero_iff.mp h0) (by simp [hz, hw])
  · exact (div_eq_one_iff_eq hw).mp h1

end Powers

end CFSG.ComponentClassification.GMS78.VLike
