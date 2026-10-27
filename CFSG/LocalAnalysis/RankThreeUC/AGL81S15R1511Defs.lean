module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def K3DvdL3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsLThreeTwoPow S → 3 ∣ Nat.card S

@[expose] def U4Data (X : Type) [Group X] [Finite X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ d.1 = .twistedA 3 q ∧ 3 ∣ q.card + 1) ∧
    Nonempty ((↥(pElementSubgroup 3 (⊤ : Subgroup X)) ⧸
      CFSG.pCore 2 ↥(pElementSubgroup 3 (⊤ : Subgroup X))) ≃* (TauCeti.CFSGIndex.lie d).Group)

end CFSG.LocalAnalysis.RankThreeUC.S15
