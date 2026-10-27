module

public import CFSG.LieType.Ree.SmallReeFixedCoordinates

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] [Finite K] {a : ℕ}

omit [Finite K] in
theorem smallReeSigma_zero : smallReeSigma a (0 : K) = 0 :=
  zero_pow (by positivity)

omit [Finite K] in
theorem smallReeCoord_zero
    : smallReeCoord a K 0 0 0 = 1 := by
  simp [smallReeCoord, smallReeSigma_zero, smallReeX_zero]

theorem smallReeCoord_mul
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (t b c s d e : K) :
    smallReeCoord a K t b c * smallReeCoord a K s d e =
      smallReeCoord a K (t + s) (b + d + smallReeSigma a t * s)
        (c + e - b * s + smallReeSigma a t * s ^ 2) := by
  obtain ⟨hchar, ρ, σ, -, hσ, -, -, hσσ, -⟩ := small_Ree_field_power_identities a K hK
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hs : ∀ x, smallReeSigma a x = σ x := fun x => (hσ x).symm
  simp only [smallReeCoord_eq_smallReeP]
  rw [smallReeP_mul h3]
  simp only [hs, map_add, map_sub, map_mul, map_pow, hσσ]
  congr 1
  · ring
  · ring
  · linear_combination (t ^ 2 * s + t * s ^ 2) * (σ t + σ s) * h3
  · linear_combination ((t ^ 3 + s ^ 3) * σ t * σ s + (t ^ 2 * s + t * s ^ 2) * (σ t + σ s) ^ 2) *
      h3

theorem smallReeCoord_inv
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (t b c : K) :
    (smallReeCoord a K t b c)⁻¹ = smallReeCoord a K (-t) (-b + t * smallReeSigma a t)
      (-c - b * t - t ^ 2 * smallReeSigma a t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [smallReeCoord_mul hK, ← smallReeCoord_zero (K := K) (a := a)]
  congr 1 <;> ring

theorem smallReeCoord_pow_three
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (t b c : K) :
    smallReeCoord a K t b c ^ 3 = smallReeCoord a K 0 0 (-(t ^ 2 * smallReeSigma a t)) := by
  obtain ⟨hchar, ρ, σ, -, hσ, -, -, -, -⟩ := small_Ree_field_power_identities a K hK
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hs : ∀ x, smallReeSigma a x = σ x := fun x => (hσ x).symm
  rw [pow_three', smallReeCoord_mul hK, smallReeCoord_mul hK]
  simp only [hs, map_add]
  congr 1
  · linear_combination t * h3
  · linear_combination (b + σ t * t) * h3
  · linear_combination (c - b * t + σ t * t ^ 2) * h3

theorem small_Ree_positive_coordinate_product
    (a : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (∀ t b c s d e : K, smallReeCoord a K t b c * smallReeCoord a K s d e =
      smallReeCoord a K (t + s) (b + d + smallReeSigma a t * s)
        (c + e - b * s + smallReeSigma a t * s ^ 2)) ∧
    smallReeCoord a K 0 0 0 = 1 ∧
    (∀ t b c : K, (smallReeCoord a K t b c)⁻¹ = smallReeCoord a K (-t)
      (-b + t * smallReeSigma a t) (-c - b * t - t ^ 2 * smallReeSigma a t)) ∧
    ∀ t b c : K,
      smallReeCoord a K t b c ^ 3 = smallReeCoord a K 0 0 (-(t ^ 2 * smallReeSigma a t)) :=
  ⟨smallReeCoord_mul hK, smallReeCoord_zero, smallReeCoord_inv hK, smallReeCoord_pow_three hK⟩

end CFSG.LieType.Ree
