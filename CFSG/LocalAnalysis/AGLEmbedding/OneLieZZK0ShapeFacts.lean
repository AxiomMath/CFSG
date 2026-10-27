module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactOneLieListInvolve : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      ((∃ d : TauCeti.ValidLieTypeIndex, (IsSpFourIndex p d ∨ IsP1ChevTwoIndex p d) ∧
          Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
        Nonempty (L ≃* alternatingGroup (Fin (3 * p))) ∨
        (∃ s : TauCeti.SporadicName, P1ThreeSporList p s ∧ ¬ (p = 3 ∧ s = .M) ∧
          Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic s).Group))) →
      ∀ (Y : Subgroup L) (φ : Y →* K), Function.Surjective φ →
        p.Coprime (Nat.card φ.ker) → False

@[expose] def KFactRankOneCoreProper : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ d : TauCeti.ValidLieTypeIndex,
      ((∃ n, IsLinTwoIndex p n d) ∨ IsUnitaryIndex p d ∨ IsReeGTwoIndex p d) →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ T : Sylow p L,
        GLBCore p 1 (T : Subgroup L) ≠ ⊤

@[expose] def KFactOneLieCenterOver : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
      IsCatalogGroup L → ∀ T₁ : Sylow p L,
        ¬ IsCyclic (T₁ : Subgroup L) → GLBCore p 1 (T₁ : Subgroup L) ≠ ⊤ →
        ¬ Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2 →
      ∀ (Y : Subgroup L) (φ : Y →* K), Function.Surjective φ →
        p.Coprime (Nat.card φ.ker) →
        (T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) ≤ Y →
        Y = ⊤ ∨ (IsUnitaryGroup p L ∧
          Nat.card ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) :
            Subgroup L) = Nat.card (T : Subgroup K))

end CFSG.AGLEmbedding
