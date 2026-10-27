module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def K21bGeom : Prop :=
  ∀ (S : Type) [Group S] [Finite S], KFactsSmall.IsLThreeTwoPower S →
    ∀ E U : Subgroup S, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ → KFactsSmall.Permutable E U →
      E ≤ Subgroup.normalizer (U : Set S)

end CFSG.LocalAnalysis.RankThreeUC.S15
