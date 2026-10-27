module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Three

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

@[expose] def KFactL34Exp3 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsL34Index d →
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ x : X, IsPGroup 3 (Subgroup.zpowers x) → x ^ 3 = 1

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
