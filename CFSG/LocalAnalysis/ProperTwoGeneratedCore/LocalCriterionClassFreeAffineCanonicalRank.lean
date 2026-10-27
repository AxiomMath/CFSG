module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineNumericRank

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.Open CFSG.TwoRankLowerBound.Helpers
open CFSG.BenderSuzuki.PFchapter1section1

variable {F : Type*} [Group F] [Finite F]

theorem not_twoRankAtLeastTwo_of_twoRank_le_one
    (hrank : twoRank F ≤ 1) : ¬ TwoRankAtLeastTwo F := by
  rintro ⟨E, hcard, hsquare⟩
  have hinv (a : E) : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsquare a)
  have hE : IsElemAbelian 2 E := by
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro a b
      calc
        a * b = (a * b)⁻¹ := (hinv (a * b)).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [hinv b, hinv a]
    · intro a ha
      exact congrArg E.subtype (hsquare ⟨a, ha⟩)
  have htwo : 2 ≤ twoRank F :=
    le_twoRank_of_elementary F E hE 2 (by simpa only [Nat.reducePow] using hcard)
  omega

theorem twoRank_le_one_iff_not_twoRankAtLeastTwo :
    twoRank F ≤ 1 ↔ ¬ TwoRankAtLeastTwo F :=
  ⟨not_twoRankAtLeastTwo_of_twoRank_le_one,
    twoRank_le_one_of_not_twoRankAtLeastTwo⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
