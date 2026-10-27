module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def LieOddRankChevLinEasy : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ (l : ℕ) (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A l Q).Valid), Q.p = 2 →
      Nonempty ((K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A l Q, hv⟩) →
      ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ (r ∣ Q.card - 1 ∧ r ∣ l + 1) →
        CFSG.Open.pRank r (⊤ : Subgroup K) =
          rkLin (l + 1) true Q.card r (Nat.card (Subgroup.center K))

@[expose] def LieOddRankChevUniEasy : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ (l : ℕ) (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA l Q).Valid), Q.p = 2 →
      Nonempty ((K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA l Q, hv⟩) →
      ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ (r ∣ Q.card + 1 ∧ r ∣ l + 1) →
        CFSG.Open.pRank r (⊤ : Subgroup K) =
          rkLin (l + 1) false Q.card r (Nat.card (Subgroup.center K))

@[expose] def LieOddRankChevLinCore : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ (l : ℕ) (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A l Q).Valid), Q.p = 2 →
      Nonempty ((K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A l Q, hv⟩) →
      ∀ r : ℕ, r.Prime → r ≠ 2 → (r ∣ Q.card - 1 ∧ r ∣ l + 1) →
        CFSG.Open.pRank r (⊤ : Subgroup K) =
          rkLin (l + 1) true Q.card r (Nat.card (Subgroup.center K))

@[expose] def LieOddRankChevUniCore : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ (l : ℕ) (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA l Q).Valid), Q.p = 2 →
      Nonempty ((K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA l Q, hv⟩) →
      ∀ r : ℕ, r.Prime → r ≠ 2 → (r ∣ Q.card + 1 ∧ r ∣ l + 1) →
        CFSG.Open.pRank r (⊤ : Subgroup K) =
          rkLin (l + 1) false Q.card r (Nat.card (Subgroup.center K))

@[expose] def LieOddRankChevG2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 Q).Valid), Q.p = 2 →
      Nonempty ((K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 Q, hv⟩) →
      ∀ r : ℕ, r.Prime → r ≠ 2 →
        CFSG.Open.pRank r (⊤ : Subgroup K) = rkG2 Q.card r

@[expose] def LieOddRankChevRes : Prop :=
  LieOddRankChevLinCore ∧ LieOddRankChevUniCore ∧ LieOddRankChevG2

end CFSG.LocalAnalysis.RankThreeUC.S15
