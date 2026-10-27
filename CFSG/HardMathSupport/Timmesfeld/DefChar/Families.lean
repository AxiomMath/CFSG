module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefChar
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

inductive DefCharFamily where
  | A | twistedA | B | C | D | twistedD | E6 | E7 | E8 | F4 | G2 | twistedE6 | trialityD4
  | reeG2
  deriving DecidableEq

@[expose] def DefCharFamily.Matches : DefCharFamily → TauCeti.LieTypeIndex → Prop
  | .A, d => ∃ r q, d = .A r q
  | .twistedA, d => ∃ r q, d = .twistedA r q
  | .B, d => ∃ r q, d = .B r q
  | .C, d => ∃ r q, d = .C r q
  | .D, d => ∃ r q, d = .D r q
  | .twistedD, d => ∃ r q, d = .twistedD r q
  | .E6, d => ∃ q, d = .E6 q
  | .E7, d => ∃ q, d = .E7 q
  | .E8, d => ∃ q, d = .E8 q
  | .F4, d => ∃ q, d = .F4 q
  | .G2, d => ∃ q, d = .G2 q
  | .twistedE6, d => ∃ q, d = .twistedE6 q
  | .trialityD4, d => ∃ q, d = .trialityD4 q
  | .reeG2, d => ∃ m, d = .reeG2 m

theorem exists_family_of_characteristic_ne_two (d : TauCeti.LieTypeIndex)
    (hd : d.characteristic ≠ 2) : ∃ k : DefCharFamily, k.Matches d := by
  cases d with
  | A r q => exact ⟨.A, r, q, rfl⟩
  | twistedA r q => exact ⟨.twistedA, r, q, rfl⟩
  | B r q => exact ⟨.B, r, q, rfl⟩
  | C r q => exact ⟨.C, r, q, rfl⟩
  | D r q => exact ⟨.D, r, q, rfl⟩
  | twistedD r q => exact ⟨.twistedD, r, q, rfl⟩
  | E6 q => exact ⟨.E6, q, rfl⟩
  | E7 q => exact ⟨.E7, q, rfl⟩
  | E8 q => exact ⟨.E8, q, rfl⟩
  | F4 q => exact ⟨.F4, q, rfl⟩
  | G2 q => exact ⟨.G2, q, rfl⟩
  | twistedE6 q => exact ⟨.twistedE6, q, rfl⟩
  | trialityD4 q => exact ⟨.trialityD4, q, rfl⟩
  | suzuki m => exact absurd (by simp) hd
  | reeG2 m => exact ⟨.reeG2, m, rfl⟩
  | reeF4 m => exact absurd (by simp) hd
  | tits => exact absurd (by simp) hd

@[expose] def DefCharOuterRankFam (k : DefCharFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
        ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 3 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

@[expose] def DefCharInnerCoreFreeFam (k : DefCharFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
        ∀ x ∈ innerAut S, orderOf x = p → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
          GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥

theorem defCharOuterRank_of_families (h : ∀ k, DefCharOuterRankFam k) : DefCharOuterRank := by
  intro S _ _ hS hnab idx hidx p hp hp2 hch D hD hcard
  have hne : idx.1.characteristic ≠ 2 := by rw [hch]; exact hp2
  obtain ⟨k, hk⟩ := exists_family_of_characteristic_ne_two idx.1 hne
  exact h k S hS hnab idx hk hidx p hp hp2 hch D hD hcard

theorem defCharInnerCoreFree_of_families (h : ∀ k, DefCharInnerCoreFreeFam k) :
    DefCharInnerCoreFree := by
  intro S _ _ hS hnab idx hidx p hp hp2 hch x hx hxo H hH
  have hne : idx.1.characteristic ≠ 2 := by rw [hch]; exact hp2
  obtain ⟨k, hk⟩ := exists_family_of_characteristic_ne_two idx.1 hne
  exact h k S hS hnab idx hk hidx p hp hp2 hch x hx hxo H hH

end CFSG.HardMathSupport.Timmesfeld.DefChar
