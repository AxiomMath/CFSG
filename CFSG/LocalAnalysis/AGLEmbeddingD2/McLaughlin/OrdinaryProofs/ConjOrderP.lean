module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

variable {N : Type} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]

theorem pRank_le_one_of_open_eq_one {N₀ : Subgroup N} (h1 : CFSG.Open.pRank p N₀ = 1) :
    CFSG.pRank p ↥N₀ ≤ 1 := by
  have hp' : p.Prime := Fact.out
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top p hp'.one_lt N₀]
  exact h1.le

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

end
