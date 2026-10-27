module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def IsLocallyBalancedAbs (p k : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D = p ^ k →
    ∀ H : Subgroup (MulAut K), innerAut K ≤ H → D ≤ Subgroup.normalizer (H : Set (MulAut K)) →
      localDeltaIn p H D = ⊥

theorem IsLocallyBalancedAbs.isLocallyBalanced {p k : ℕ} {K : Type*} [Group K]
    (h : IsLocallyBalancedAbs p k K) (A : Subgroup (MulAut K)) : IsLocallyBalanced p k A :=
  fun D hD H hH hDH => h D hD.2.1 hD.2.2 H hH hDH

@[expose] def LocalThreeBalanceSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → (∀ n : ℕ, IsEmpty (S ≃* ↥(alternatingGroup (Fin n)))) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → IsLocallyBalancedAbs p 3 S

@[expose] def LocalThreeBalanceAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProper G → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian p B →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → 3 ≤ CFSG.Open.pRank p B →
      ∀ L : Subgroup G, GLAPComponent p X L → ∀ n : ℕ,
        Nonempty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n))) →
          IsCompLocallyBalanced p 3 B L

@[expose] def LocalThreeBalanceDefChar : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p → IsLocallyBalancedAbs p 3 S

@[expose] def LocalThreeBalanceCrossChar : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic ≠ p → IsLocallyBalancedAbs p 3 S

@[expose] def LocalThreeBalanceSporadic : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ name : TauCeti.SporadicName, Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → IsLocallyBalancedAbs p 3 S

end CFSG.HardMathSupport.Timmesfeld.Coordinator
