module

public import CFSG.CharacterTheory.Wreathed.MaximalOrderCount

public noncomputable section

namespace CFSG.Wreathed

open scoped BigOperators Classical

theorem sum_two_value_function {G : Type*} [Group G] [Fintype G]
    (limit : ℕ) (hlimit : 1 < limit) (f : G → ℂ) (δ ζ : ℂ)
    (hbound : ∀ g : G, orderOf g ≤ limit)
    (hlow : ∀ g : G, g ≠ 1 → orderOf g < limit → f g = δ)
    (hmax : ∀ g : G, orderOf g = limit → f g = δ * ζ) :
    ∑ g : G, f g = (Nat.card G : ℂ) * δ +
      (Nat.card {g : G // orderOf g = limit} : ℂ) * (δ * ζ - δ) + f 1 - δ := by
  have hone : orderOf (1 : G) ≠ limit := by
    simp only [orderOf_one]
    omega
  have hpoint (g : G) : f g = δ +
      (if orderOf g = limit then δ * ζ - δ else 0) +
      (if g = 1 then f 1 - δ else 0) := by
    by_cases hg : g = 1
    · subst g
      simp only [hone, ↓reduceIte]
      ring
    · by_cases ho : orderOf g = limit
      · rw [hmax g ho]
        simp only [ho, hg, ↓reduceIte]
        ring
      · rw [hlow g hg (by have hb := hbound g; omega)]
        simp only [ho, hg, ↓reduceIte, add_zero]
  have hsum : (∑ g : G, if orderOf g = limit then δ * ζ - δ else 0) =
      (Nat.card {g : G // orderOf g = limit} : ℂ) * (δ * ζ - δ) := by
    simp [Finset.sum_ite, Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun g _ => hpoint g)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

theorem character_sum_integer_multiple {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ a : ℤ, ∑ g : G, ρ.character g = (Nat.card G : ℂ) * (a : ℂ) := by
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  have havg := Representation.card_inv_mul_sum_char_eq_finrank ρ
  refine ⟨(Module.finrank ℂ ρ.invariants : ℤ), ?_⟩
  calc
    ∑ g : G, ρ.character g =
        (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g) := by
      rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    _ = (Nat.card G : ℂ) * (Module.finrank ℂ ρ.invariants : ℂ) := by rw [havg]
    _ = _ := by simp only [Int.cast_natCast]

theorem two_value_character_degree_congruence (n : ℕ) (hn : 1 ≤ n)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (CFSG.Open.WreathedTwoGroup n) V) (δ ζ : ℤ)
    (hlow : ∀ g : CFSG.Open.WreathedTwoGroup n,
      g ≠ 1 → orderOf g < 2 * 2 ^ n → ρ.character g = (δ : ℂ))
    (hmax : ∀ g : CFSG.Open.WreathedTwoGroup n,
      orderOf g = 2 * 2 ^ n → ρ.character g = (δ * ζ : ℤ)) :
    (Module.finrank ℂ V : ℤ) ≡
      δ + (((2 ^ n) ^ 2 / 2 : ℕ) : ℤ) * δ * (1 - ζ)
      [ZMOD ((2 * (2 ^ n) ^ 2 : ℕ) : ℤ)] := by
  let : Fintype (CFSG.Open.WreathedTwoGroup n) := Fintype.ofFinite _
  have hpos := pow_pos (by decide : 0 < (2 : ℕ)) n
  have hbound (g : CFSG.Open.WreathedTwoGroup n) : orderOf g ≤ 2 * 2 ^ n :=
    orderOf_le_of_pow_eq_one (by omega) (element_pow_twice_modulus (2 ^ n) g)
  have hsum := sum_two_value_function (2 * 2 ^ n) (by omega) ρ.character
    (δ : ℂ) (ζ : ℂ) hbound hlow (by simpa only [Int.cast_mul] using hmax)
  obtain ⟨a, ha⟩ := character_sum_integer_multiple ρ
  rw [card_wreath (2 ^ n), card_maximal_order_height n hn,
    Representation.char_one] at hsum
  rw [card_wreath (2 ^ n)] at ha
  have heq : (Module.finrank ℂ V : ℤ) - δ +
      (((2 ^ n) ^ 2 / 2 : ℕ) : ℤ) * (δ * ζ - δ) =
      ((2 * (2 ^ n) ^ 2 : ℕ) : ℤ) * (a - δ) := by
    apply Int.cast_injective (α := ℂ)
    rw [ha] at hsum
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linear_combination -hsum
  rw [Int.modEq_iff_dvd]
  refine ⟨δ - a, ?_⟩
  linear_combination -heq

end CFSG.Wreathed
