module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityEigenmultiplicities
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsAlgebra
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityMultiplicities

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalSquareRoot

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.SquareRootSmallCharacterRigidity
  CFSG.Wreathed.ConditionalFourier

theorem dvd_add_iff_of_lt {m j t : ℕ} (hj1 : 1 ≤ j) (hjm : j < m) (ht : t < 2 * m) :
    m ∣ j + t ↔ t = m - j ∨ t = 2 * m - j := by
  constructor
  · rintro ⟨q, hq⟩
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h, mul_zero] at hq
        omega
      · exact h
    have hq2 : q < 3 := by
      by_contra h
      push Not at h
      have : m * 3 ≤ m * q := Nat.mul_le_mul_left m h
      omega
    interval_cases q <;> omega
  · rintro (rfl | rfl)
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩

theorem dvd_iff_of_lt {m t : ℕ} (hm : 1 ≤ m) (ht : t < 2 * m) : m ∣ t ↔ t = 0 ∨ t = m := by
  constructor
  · rintro ⟨q, hq⟩
    have hq2 : q < 2 := by
      by_contra h
      push Not at h
      have : m * 2 ≤ m * q := Nat.mul_le_mul_left m h
      omega
    interval_cases q <;> omega
  · rintro (rfl | rfl)
    · exact dvd_zero m
    · exact dvd_refl _

theorem fourier_character_square_powers {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) {m : ℕ} (hm : 1 ≤ m)
    (hy : y ^ (2 * m) = 1) {η : ℂ} (hη : IsPrimitiveRoot η (2 * m)) {j : ℕ} (hj1 : 1 ≤ j)
    (hjm : j < m) :
    (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m, ((η ^ 2) ^ (j * k) - 1) * data.character (y ^ (2 * k)) =
      (((cyclicEigenmultiplicity data y η (m - j) : ℤ) +
        cyclicEigenmultiplicity data y η (2 * m - j) - cyclicEigenmultiplicity data y η 0 -
        cyclicEigenmultiplicity data y η m : ℤ) : ℂ) := by
  set ν := fun t => (cyclicEigenmultiplicity data y η t : ℂ) with hν
  have hζ : IsPrimitiveRoot (η ^ 2) m := hη.pow (by omega) rfl
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hexp : ∀ k : ℕ, data.character (y ^ (2 * k)) =
      ∑ t ∈ Finset.range (2 * m), ν t * (η ^ 2) ^ (t * k) := by
    intro k
    rw [character_cyclic_eigenmultiplicity_expansion data y (2 * m) (by omega) hy η hη (2 * k)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← pow_mul, show t * (2 * k) = 2 * (t * k) by ring]
  have hswap : ∑ k ∈ Finset.range m, ((η ^ 2) ^ (j * k) - 1) * data.character (y ^ (2 * k)) =
      ∑ t ∈ Finset.range (2 * m), ν t *
        (∑ k ∈ Finset.range m, (η ^ 2) ^ ((j + t) * k) -
          ∑ k ∈ Finset.range m, (η ^ 2) ^ (t * k)) := by
    simp only [hexp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [add_mul, pow_add]
    ring
  rw [hswap]
  simp only [sum_range_pow_mul hζ]
  have hind1 : ∀ t ∈ Finset.range (2 * m), (if m ∣ j + t then (m : ℂ) else 0) =
      (if t = m - j then (m : ℂ) else 0) + (if t = 2 * m - j then (m : ℂ) else 0) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    by_cases h1 : t = m - j
    · rw [ite_eq_left ((dvd_add_iff_of_lt hj1 hjm ht').mpr (Or.inl h1)), ite_eq_left h1,
        ite_eq_right (by omega), add_zero]
    · by_cases h2 : t = 2 * m - j
      · rw [ite_eq_left ((dvd_add_iff_of_lt hj1 hjm ht').mpr (Or.inr h2)), ite_eq_right h1,
          ite_eq_left h2,
          zero_add]
      · rw [ite_eq_right (fun h => by rcases (dvd_add_iff_of_lt hj1 hjm ht').mp h with h | h <;>
          contradiction), ite_eq_right h1, ite_eq_right h2, add_zero]
  have hind2 : ∀ t ∈ Finset.range (2 * m), (if m ∣ t then (m : ℂ) else 0) =
      (if t = 0 then (m : ℂ) else 0) + (if t = m then (m : ℂ) else 0) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    by_cases h1 : t = 0
    · rw [ite_eq_left ((dvd_iff_of_lt hm ht').mpr (Or.inl h1)), ite_eq_left h1,
        ite_eq_right (by omega),
        add_zero]
    · by_cases h2 : t = m
      · rw [ite_eq_left ((dvd_iff_of_lt hm ht').mpr (Or.inr h2)), ite_eq_right h1, ite_eq_left h2,
          zero_add]
      · rw [ite_eq_right (fun h => by rcases (dvd_iff_of_lt hm ht').mp h with h | h <;>
          contradiction), ite_eq_right h1, ite_eq_right h2, add_zero]
  rw [Finset.sum_congr rfl fun t ht => by rw [hind1 t ht, hind2 t ht]]
  simp only [mul_sub, mul_add, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_range]
  rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
    ite_eq_left (by omega)]
  push_cast
  field_simp
  ring

theorem modEq_two_of_add_mul {F₀ F₁ A ε : ℤ} {q : ℕ} (hq : Odd q) (hε : ε = 1 ∨ ε = -1)
    (h : F₀ + (1 + ε * q) * F₁ = A) : F₀ ≡ A [ZMOD 2] := by
  obtain ⟨k, hk⟩ := hq
  rw [Int.modEq_iff_dvd]
  rcases hε with rfl | rfl
  · exact ⟨(k + 1) * F₁, by rw [← h, hk]; push_cast; ring⟩
  · exact ⟨-k * F₁, by rw [← h, hk]; push_cast; ring⟩

end CFSG.Wreathed.ConditionalSquareRoot
