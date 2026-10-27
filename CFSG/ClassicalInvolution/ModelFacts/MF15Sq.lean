module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem ringChar_ne_two_of_two_ne_zero (h2 : (2 : F) ≠ 0) : ringChar F ≠ 2 := by
  intro h
  apply h2
  have := (ringChar.spec F 2).mpr (by rw [h])
  simpa using this

theorem isSquare_mul_of_not {a b : F} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a * b) := by
  classical
  have := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by rw [h, mul_zero]⟩
  have hb0 : b ≠ 0 := fun h => hb ⟨0, by rw [h, mul_zero]⟩
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha, quadraticChar_neg_one_iff_not_isSquare.mpr hb]
  norm_num

theorem isSquare_neg_of_not {s : F} (hs : ¬ IsSquare s)
    (h1 : ¬ IsSquare (-1 : F)) : IsSquare (-s) := by
  have := isSquare_mul_of_not h1 hs
  simpa using this

end CFSG.ClassicalInvolution.ModelFacts.MF15
