module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactSp62AutElemRank : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsSpSixTwoIndex d →
    Nonempty (L ≃* CatGroup d) → CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 3

end CFSG.AGLEmbedding
