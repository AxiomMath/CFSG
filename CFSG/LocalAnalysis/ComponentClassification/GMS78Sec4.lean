module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push29Defs

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

theorem not_psl2_of_l2Res (h : L2Res) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
      Open.standardComponentOddCore G = ⊥ → ∀ m : ℕ, 3 ≤ m →
        ¬ StatedClassicalModel (rankTwoQuot A) .PSL 2 2 m := by
  intro G _ _ A hA hO m hm hS
  exact h G A ⟨hA.standard, hO, hA.not_normal, hA.rank, Or.inl ⟨m, hm, hS⟩⟩ m hm
    (nonempty_mulEquiv_psl2_of_stated hS)

end CFSG.ComponentClassification.GMS78
