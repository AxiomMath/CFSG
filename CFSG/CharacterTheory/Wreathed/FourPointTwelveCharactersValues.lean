module

public import CFSG.CharacterTheory.Wreathed.FourPointThreePairsRoot

public section

namespace CFSG.Wreathed.FourPointTwelveCharacters

open CFSG.Wreathed.FourPointGaussianColumns

theorem floor_re_intCast (k : ℤ) : ⌊((k : ℂ)).re⌋ = k := by
  simp

theorem cast_floor_re {t : ℂ} (h : ∃ k : ℤ, t = k) : ((⌊t.re⌋ : ℤ) : ℂ) = t := by
  obtain ⟨k, rfl⟩ := h
  rw [floor_re_intCast]

theorem cast_floor {r : ℝ} (h : ∃ k : ℤ, r = k) : ((⌊r⌋ : ℤ) : ℝ) = r := by
  obtain ⟨k, rfl⟩ := h
  simp

theorem cast_floor_complex {r : ℝ} (h : ∃ k : ℤ, r = k) : ((⌊r⌋ : ℤ) : ℂ) = (r : ℂ) := by
  rw [← cast_floor h]
  simp

theorem sum_mul_intCast_eq {ι : Type*} (B : Finset ι) {f g : ι → ℤ} {F G : ι → ℂ}
    (hf : ∀ χ ∈ B, (f χ : ℂ) = F χ) (hg : ∀ χ ∈ B, (g χ : ℂ) = G χ) {c : ℤ}
    (h : ∑ χ ∈ B, F χ * G χ = c) : ∑ χ ∈ B, f χ * g χ = c := by
  have h' : ((∑ χ ∈ B, f χ * g χ : ℤ) : ℂ) = c := by
    push_cast
    rw [← h]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hf χ hχ, hg χ hχ]
  exact_mod_cast h'

theorem normSq_eq_re_sq_add_imCoeff_sq {i : ℂ} (hi : i ^ 2 = -1) (t : ℂ) :
    Complex.normSq t = t.re ^ 2 + imCoeff i t ^ 2 := by
  obtain ⟨-, h1⟩ := re_eq_zero_and_im_sq_eq_one hi
  have hne := im_ne_zero hi
  rw [Complex.normSq_apply, imCoeff, div_pow, h1, div_one]
  ring

theorem values_of_row {i : ℂ} (hi : i ^ 2 = -1) {T U A B : ℂ} {l₁ l₂ l₃ a₁ a₂ a₃ s : ℤ}
    (h₁₃ : (a₁ : ℂ) - a₃ = ((4 * imCoeff i U - imCoeff i T) / 6 : ℝ))
    (hT : T = -2 * (l₂ : ℂ) + 2 * s - a₂ - a₁ - a₃ + 2 * i * (((l₃ : ℂ) - l₁) + ((a₃ : ℂ) - a₁)))
    (hA : A = 2 * ((l₂ : ℂ) - l₁ - l₃) - 2 * s + 3 * a₂ - a₁ - a₃)
    (hB : B = ((l₂ : ℂ) - l₁ - l₃ - 3 * a₂ + a₁ + a₃) / 2 + s)
    (hU : (U.re : ℂ) = (-(l₂ : ℂ) - 2 * s + a₂ + a₁ + a₃) / 2) :
    T = ((-2 * l₂ + 2 * s - a₂ - a₁ - a₃ : ℤ) : ℂ) +
        ((2 * ((l₃ - l₁) + (a₃ - a₁)) : ℤ) : ℂ) * i ∧
      A = ((2 * (l₂ - l₁ - l₃) - 2 * s + 3 * a₂ - a₁ - a₃ : ℤ) : ℂ) ∧
      2 * B = ((l₂ - l₁ - l₃ - 3 * a₂ + a₁ + a₃ + 2 * s : ℤ) : ℂ) ∧
      2 * U = ((-l₂ - 2 * s + a₂ + a₁ + a₃ : ℤ) : ℂ) +
        ((2 * (a₁ - a₃) + (l₃ - l₁) : ℤ) : ℂ) * i := by
  have hT' : T = (((-2 * l₂ + 2 * s - a₂ - a₁ - a₃ : ℤ) : ℝ) : ℂ) +
      (((2 * ((l₃ - l₁) + (a₃ - a₁)) : ℤ) : ℝ) : ℂ) * i := by
    rw [hT]
    push_cast
    ring
  have hTim : imCoeff i T = ((2 * ((l₃ - l₁) + (a₃ - a₁)) : ℤ) : ℝ) := by
    rw [hT', imCoeff_add_mul hi]
  have hUim : imCoeff i U = (((2 * (a₁ - a₃) + (l₃ - l₁) : ℤ) : ℝ)) / 2 := by
    have h' : ((a₁ : ℝ) - a₃) = (4 * imCoeff i U - imCoeff i T) / 6 := by exact_mod_cast h₁₃
    rw [hTim] at h'
    push_cast at h' ⊢
    linarith
  refine ⟨by rw [hT]; push_cast; ring, by rw [hA]; push_cast; ring, by rw [hB]; push_cast; ring,
    ?_⟩
  rw [FourPointThreePairs.eq_re_add_imCoeff_mul hi U, mul_add, ← mul_assoc, hU, hUim]
  push_cast
  ring

end CFSG.Wreathed.FourPointTwelveCharacters
