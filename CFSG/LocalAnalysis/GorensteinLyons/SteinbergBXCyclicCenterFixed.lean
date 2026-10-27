module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCBExponentFourLayer

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement Pointwise

variable {D : Type*} [Group D]

theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

end CFSG.LocalAnalysis.GorensteinLyons
