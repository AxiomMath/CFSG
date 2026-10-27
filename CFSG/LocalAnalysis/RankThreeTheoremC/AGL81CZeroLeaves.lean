module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable (G : Type) [Group G] [Finite G]

@[expose] def KFactSUThreeTwoShape : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    Subgroup.closure {x : ↥(StatedSU 3 2 K) | ∃ k : ℕ, x ^ (2 ^ k) = 1} = ⊤ ∧
      ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup ↥(StatedSU 3 2 K)),
        x ^ 3 = 1

end CFSG.LocalAnalysis.RankThreeTheoremC
