module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def DefCharOuterRank : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
        ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 3 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

@[expose] def DefCharInnerCoreFree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
        ∀ x ∈ innerAut S, orderOf x = p → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
          GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥

theorem localThreeBalanceDefChar_of (hOut : DefCharOuterRank) (hCore : DefCharInnerCoreFree) :
    LocalThreeBalanceDefChar := by
  intro S _ _ hS hnab idx hidx p hp hp2 hch D hD hcard H hH _
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, ⟨hxD, hxI⟩, hx1⟩ := hOut S hS hnab idx hidx p hp hp2 hch D hD hcard
  have hxp : orderOf x = p := orderOf_eq_prime (hD.2 x hxD) hx1
  have hle : localDeltaIn p H D ≤
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) := by
    unfold localDeltaIn
    exact iInf₂_le_of_le x hxD (iInf_le_of_le hx1 le_rfl)
  rw [hCore S hS hnab idx hidx p hp hp2 hch x hxI hxp H hH] at hle
  exact le_bot_iff.1 hle

end CFSG.HardMathSupport.Timmesfeld.Coordinator
