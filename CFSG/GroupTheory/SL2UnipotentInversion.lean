module

public import CFSG.CGT.Timmesfeld75.L2Defs
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GroupTheory

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

theorem utriElt_conj_eq_inv_of_mul_eq {F : Type} [Field F] [CharP F 2] {x : SL(2, F)} {s : F}
    (hs : s * x 1 0 = x 0 0 + x 1 1) : utriElt s * x * (utriElt s)⁻¹ = x⁻¹ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine CFSG.CGT.Timmesfeld75.sl2_ext ?_ ?_ ?_ ?_ <;> sl2_simp
  · linear_combination hs + x 0 0 * h2
  · linear_combination (-s) * hs + (x 0 1 - s * x 0 0) * h2
  · linear_combination x 1 0 * h2
  · linear_combination -hs - x 0 0 * h2

theorem exists_utriElt_conj_eq_inv {F : Type} [Field F] [Finite F] [CharP F 2] {x : SL(2, F)}
    (hx : orderOf x = Nat.card F + 1) : ∃ s : F, utriElt s * x * (utriElt s)⁻¹ = x⁻¹ := by
  have hne : x 1 0 ≠ 0 := CFSG.SeitzReduction.F4Pilot.apply_one_zero_ne_zero_of_orderOf_eq hx
  exact ⟨(x 0 0 + x 1 1) / x 1 0, utriElt_conj_eq_inv_of_mul_eq (div_mul_cancel₀ _ hne)⟩

end CFSG.GroupTheory
