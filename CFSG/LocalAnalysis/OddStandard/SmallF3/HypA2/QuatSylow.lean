module

public import CFSG.CharacterTheory.TwoRankLowerBound.RankOneClassification
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.ChevalleyBinomial
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem exists_quaternion_sylow {K : Type} [Group K] [Finite K] (hK : Group.IsPerfect K)
    (hev : Even (Nat.card K)) (hr : CFSG.pRank 2 K ≤ 1) :
    ∃ (T : Sylow 2 K) (r : ℕ), 3 ≤ r ∧
      Nonempty (↥(T : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hrank : CFSG.Open.twoRank K ≤ 1 := by
    rw [CFSG.Open.twoRank]
    exact (CFSG.SectionRank.pRank_eq_open_pRank_top 2 K) ▸ hr
  haveI : Group.IsPerfect K := hK
  obtain ⟨T⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨r, hr3, e⟩ :=
    CFSG.TwoRankLowerBound.Helpers.sylow_two_quaternion_of_perfect_rank_one K hev hrank T
  exact ⟨T, r, hr3, e⟩

end CFSG.OddStandard.SmallF3.HypA2
