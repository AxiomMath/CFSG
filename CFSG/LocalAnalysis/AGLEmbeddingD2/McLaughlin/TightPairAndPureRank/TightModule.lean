module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ActionOnSub
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Quasithin
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def TightKP (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, (n = 6 ∨ n = 7 ∨ n = 8) ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group))

end CFSG.AGLEmbeddingD2.McLaughlin
