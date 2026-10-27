module

public import CFSG.CharacterTheory.Wreathed.CharacterAverage

public noncomputable section

namespace CFSG.Wreathed

theorem half_square_double (n : ℕ) (hn : 1 ≤ n) :
    ((2 ^ n) ^ 2 / 2) * 2 = (2 ^ n) ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have heq : (2 ^ (k + 1)) ^ 2 = (2 ^ k * 2 * 2 ^ k) * 2 := by
    rw [pow_succ]
    ring
  rw [heq, Nat.mul_div_cancel _ (by decide)]

theorem twice_modulus_dvd_square (n : ℕ) (hn : 1 ≤ n) :
    ((2 * 2 ^ n : ℕ) : ℤ) ∣ (((2 ^ n) ^ 2 : ℕ) : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  refine ⟨(2 ^ k : ℕ), ?_⟩
  push_cast
  simp only [Nat.succ_eq_add_one, pow_succ]
  ring

theorem signed_correction_mod_twice_modulus (n : ℕ) (hn : 1 ≤ n)
    (δ ζ : ℤ) (hζ : ζ = 1 ∨ ζ = -1) :
    δ + (((2 ^ n) ^ 2 / 2 : ℕ) : ℤ) * δ * (1 - ζ) ≡ δ
      [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  rcases hζ with rfl | rfl
  · simp
  · obtain ⟨a, ha⟩ := twice_modulus_dvd_square n hn
    have hhalf := congrArg (fun x : ℕ => (x : ℤ)) (half_square_double n hn)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hhalf
    refine ⟨-(a * δ), ?_⟩
    linear_combination -δ * hhalf - δ * ha

theorem two_value_character_degree_mod_twice_modulus (n : ℕ) (hn : 1 ≤ n)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (CFSG.Open.WreathedTwoGroup n) V) (δ ζ : ℤ)
    (hζ : ζ = 1 ∨ ζ = -1)
    (hlow : ∀ g : CFSG.Open.WreathedTwoGroup n,
      g ≠ 1 → orderOf g < 2 * 2 ^ n → ρ.character g = (δ : ℂ))
    (hmax : ∀ g : CFSG.Open.WreathedTwoGroup n,
      orderOf g = 2 * 2 ^ n → ρ.character g = (δ * ζ : ℤ)) :
    (Module.finrank ℂ V : ℤ) ≡ δ [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
  have hmod : ((2 * 2 ^ n : ℕ) : ℤ) ∣ ((2 * (2 ^ n) ^ 2 : ℕ) : ℤ) := by
    refine ⟨(2 ^ n : ℕ), ?_⟩
    push_cast
    ring
  exact (Int.ModEq.of_dvd hmod
    (two_value_character_degree_congruence n hn ρ δ ζ hlow hmax)).trans
    (signed_correction_mod_twice_modulus n hn δ ζ hζ)

end CFSG.Wreathed
