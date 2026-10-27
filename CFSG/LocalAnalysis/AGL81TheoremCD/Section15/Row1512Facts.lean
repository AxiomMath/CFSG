module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def KSMRes : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ (d : TauCeti.ValidLieTypeIndex) (l : ℕ) (Q : TauCeti.PrimePower), Q.p = 2 →
      (d.1 = .A l Q ∧ Odd Q.exponent ∨ d.1 = .twistedA l Q ∧ Even Q.exponent) →
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      Odd (Nat.card (Subgroup.center K)) → ¬ 3 ∣ Nat.card (Subgroup.center K)

@[expose] def KParU7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ∀ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 → d.1 = .twistedA 6 Q →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∃ P : Subgroup (X ⧸ gnC T), IsMinOverBorel Ls (gnImg T T ⊓ Ls) P ∧
          ∀ q : ℕ, q.Prime → q ∣ Q.card + 1 → 2 ≤ CFSG.Open.pRank q (pElementSubgroup 2 P)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
