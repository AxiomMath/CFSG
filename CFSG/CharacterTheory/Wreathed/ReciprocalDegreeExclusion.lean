module

public import CFSG.CharacterTheory.Wreathed.TwoPartArithmetic
public import CFSG.CharacterTheory.Wreathed.CharacterDegreeCongruence

public noncomputable section

namespace CFSG.Wreathed

@[expose] def modFourSign (q : ℕ) : ℤ := if q % 4 = 1 then 1 else -1

theorem modFourSign_cases (q : ℕ) : modFourSign q = 1 ∨ modFourSign q = -1 := by
  unfold modFourSign
  split <;> simp

theorem odd_mod_four_cases (q : ℕ) (hq : Odd q) : q % 4 = 1 ∨ q % 4 = 3 := by
  have hodd := Nat.odd_iff.mp hq
  have hmod := Nat.mod_lt q (by decide : 0 < (4 : ℕ))
  omega

theorem parameter_mod_twice_modulus (q n : ℕ) (hq : 3 ≤ q) (hodd : Odd q)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    (q : ℤ) ≡ modFourSign q + (2 ^ n : ℕ) [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
  rcases odd_mod_four_cases q hodd with h | h
  · simpa only [modFourSign, h, ↓reduceIte] using
      parameter_mod_twice_modulus_split q n hq h hpart
  · have hne : q % 4 ≠ 1 := by omega
    simpa only [modFourSign, hne, ↓reduceIte] using
      parameter_mod_twice_modulus_nonsplit q n hq h hpart

theorem signed_reciprocal_polynomial_mod (n : ℕ) (hn : 1 ≤ n) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) :
    (ε + (2 ^ n : ℕ)) * ((ε + (2 ^ n : ℕ)) ^ 2 +
      ε * (ε + (2 ^ n : ℕ)) + 1) ≡ 3 * ε
      [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
  obtain ⟨a, ha⟩ := twice_modulus_dvd_square n hn
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at ha ⊢
  rw [Int.modEq_iff_dvd]
  refine ⟨-3 - 4 * ε * a - (2 ^ n : ℤ) * a, ?_⟩
  rcases hε with rfl | rfl
  · linear_combination (-4 - (2 ^ n : ℤ)) * ha
  · linear_combination (4 - (2 ^ n : ℤ)) * ha

theorem reciprocal_degree_mod_twice_modulus (q n : ℕ) (hn : 1 ≤ n)
    (hq : 3 ≤ q) (hodd : Odd q)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    (q : ℤ) * ((q : ℤ) ^ 2 + modFourSign q * q + 1) ≡
      3 * modFourSign q [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
  have hqmod := parameter_mod_twice_modulus q n hq hodd hpart
  have hpoly := ((hqmod.pow 2).add (hqmod.mul_left (modFourSign q))).add_right 1
  exact (hqmod.mul hpoly).trans
    (signed_reciprocal_polynomial_mod n hn (modFourSign q) (modFourSign_cases q))

theorem degree_sign_not_triple_sign_mod (n : ℕ) (hn : 2 ≤ n) (δ ε : ℤ)
    (hδ : δ = 1 ∨ δ = -1) (hε : ε = 1 ∨ ε = -1) :
    ¬δ ≡ 3 * ε [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
  have hlarge : 4 ≤ 2 ^ n := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
  have hlargeZ : (8 : ℤ) ≤ 2 * (2 : ℤ) ^ n := by
    exact_mod_cast (by omega : 8 ≤ 2 * 2 ^ n)
  have hsmall (t : ℤ) (ht : 0 < t) (ht4 : t ≤ 4) : ¬2 * (2 : ℤ) ^ n ∣ t := by
    intro hd
    have hle := Int.le_of_dvd ht hd
    omega
  intro h
  have hdvd := Int.modEq_iff_dvd.mp h
  have hzero := Int.dvd_iff_emod_eq_zero.mp hdvd
  rcases hδ with rfl | rfl <;> rcases hε with rfl | rfl <;> norm_num at hzero
  · exact hsmall 2 (by decide) (by decide) hzero
  · exact hsmall 4 (by decide) (by decide) hzero
  · exact hsmall 4 (by decide) (by decide) hzero
  · exact hsmall 2 (by decide) (by decide) hzero

theorem two_value_character_reciprocal_degree_excluded (n : ℕ) (hn : 2 ≤ n)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (CFSG.Open.WreathedTwoGroup n) V) (δ ζ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) (hζ : ζ = 1 ∨ ζ = -1)
    (hlow : ∀ g : CFSG.Open.WreathedTwoGroup n,
      g ≠ 1 → orderOf g < 2 * 2 ^ n → ρ.character g = (δ : ℂ))
    (hmax : ∀ g : CFSG.Open.WreathedTwoGroup n,
      orderOf g = 2 * 2 ^ n → ρ.character g = (δ * ζ : ℤ))
    (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    (Module.finrank ℂ V : ℤ) ≠
      (q : ℤ) * ((q : ℤ) ^ 2 + modFourSign q * q + 1) := by
  intro hequal
  have hdeg := two_value_character_degree_mod_twice_modulus n (by omega) ρ δ ζ hζ hlow hmax
  have hrec := reciprocal_degree_mod_twice_modulus q n (by omega) hq hodd hpart
  rw [← hequal] at hrec
  exact degree_sign_not_triple_sign_mod n hn δ (modFourSign q) hδ (modFourSign_cases q)
    (hdeg.symm.trans hrec)

theorem wreath_two_value_character_degree_congruence (n : ℕ) (hn : 2 ≤ n)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (CFSG.Open.WreathedTwoGroup n) V) (δ ζ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) (hζ : ζ = 1 ∨ ζ = -1)
    (hlow : ∀ g : CFSG.Open.WreathedTwoGroup n,
      g ≠ 1 → orderOf g < 2 * 2 ^ n → ρ.character g = (δ : ℂ))
    (hmax : ∀ g : CFSG.Open.WreathedTwoGroup n,
      orderOf g = 2 * 2 ^ n → ρ.character g = (δ * ζ : ℤ)) :
    ((Module.finrank ℂ V : ℤ) ≡
      δ + (((2 ^ n) ^ 2 / 2 : ℕ) : ℤ) * δ * (1 - ζ)
        [ZMOD ((2 * (2 ^ n) ^ 2 : ℕ) : ℤ)]) ∧
    ((Module.finrank ℂ V : ℤ) ≡ δ [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)]) ∧
    ∀ (q : ℕ), 3 ≤ q → Odd q →
      2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n →
      ((q : ℤ) * ((q : ℤ) ^ 2 + modFourSign q * q + 1) ≡
        3 * modFourSign q [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)]) ∧
      (Module.finrank ℂ V : ℤ) ≠
        (q : ℤ) * ((q : ℤ) ^ 2 + modFourSign q * q + 1) := by
  refine ⟨two_value_character_degree_congruence n (by omega) ρ δ ζ hlow hmax,
    two_value_character_degree_mod_twice_modulus n (by omega) ρ δ ζ hζ hlow hmax, ?_⟩
  intro q hq hodd hpart
  exact ⟨reciprocal_degree_mod_twice_modulus q n (by omega) hq hodd hpart,
    two_value_character_reciprocal_degree_excluded n hn ρ δ ζ hδ hζ hlow hmax q hq hodd hpart⟩

end CFSG.Wreathed
