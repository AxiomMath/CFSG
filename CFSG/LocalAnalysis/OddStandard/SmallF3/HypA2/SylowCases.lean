module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix

theorem sylow_rank_cases {G : Type} [Group G] [Finite G] (D : Subgroup G) (S : Sylow 2 ↥D) :
    2 ≤ CFSG.Open.pRank 2 D ∨ IsCyclic ↥(S : Subgroup ↥D) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty (↥(S : Subgroup ↥D) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  by_cases h : 2 ≤ CFSG.Open.pRank 2 D
  · exact Or.inl h
  · push Not at h
    have hD : CFSG.Open.pRank 2 D ≤ 1 := by omega
    have hS : CFSG.Open.pRank 2 (S : Subgroup ↥D) ≤ 1 := by
      have h1 : CFSG.Open.pRank 2 (S : Subgroup ↥D) ≤
          CFSG.Open.pRank 2 (⊤ : Subgroup ↥D) :=
        CFSG.SectionRank.pRank_mono (by norm_num) le_top
      have h2 : CFSG.Open.pRank 2 (⊤ : Subgroup ↥D) = CFSG.Open.pRank 2 D :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup D).symm
      omega
    rcases cyclic_or_quaternion_of_pRank_le_one (X := ↥D) (P := (S : Subgroup ↥D)) S.isPGroup' hS
      with hc | hq
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hq)

end CFSG.OddStandard.SmallF3.HypA2
