module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3EvenModel

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

@[expose] def OvergroupL32U3Odd : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p ≠ 2 → q.card % 3 = 1 → d.1 = .twistedA 2 q →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → OvergroupL32Odd K

theorem overgroupL32U3_of_U3Odd (h : OvergroupL32U3Odd) : OvergroupL32U3 :=
  overgroupL32U3_of_odd h

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
