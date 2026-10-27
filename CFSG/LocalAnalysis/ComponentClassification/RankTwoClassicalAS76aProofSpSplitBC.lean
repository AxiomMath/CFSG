module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Universal.Spin.Twisted.Graded
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSquareZero
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Ranks

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

omit [DecidableEq ι] in
theorem rank_eq_one_of {X : Matrix ι ι K} {w : ι → K} (hw : w ≠ 0)
    (hle : ∀ v, ∃ a : K, X *ᵥ v = a • w) (hu : ∃ v, X *ᵥ v = w) : X.rank = 1 := by
  rw [Matrix.rank]
  have hR : LinearMap.range X.mulVecLin = K ∙ w := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨a, ha⟩ := hle v
      rw [Matrix.mulVecLin_apply, ha]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hu
  rw [hR, finrank_span_singleton hw]

end Ranks

end CFSG.ComponentClassification.RankTwoClassical
