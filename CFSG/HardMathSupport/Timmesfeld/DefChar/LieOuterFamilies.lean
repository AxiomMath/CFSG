module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112T1Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

inductive LieFamily where
  | A | twistedA | B | C | D | twistedD | E6 | E7 | E8 | F4 | G2 | twistedE6 | trialityD4
  | suzuki | reeG2 | reeF4 | tits
  deriving DecidableEq

@[expose] def LieFamily.Matches : LieFamily → TauCeti.LieTypeIndex → Prop
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
  | .suzuki, d => ∃ m, d = .suzuki m
  | .reeG2, d => ∃ m, d = .reeG2 m
  | .reeF4, d => ∃ m, d = .reeF4 m
  | .tits, d => d = .tits

theorem exists_lieFamily (d : TauCeti.LieTypeIndex) : ∃ k : LieFamily, k.Matches d := by
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
  | suzuki m => exact ⟨.suzuki, m, rfl⟩
  | reeG2 m => exact ⟨.reeG2, m, rfl⟩
  | reeF4 m => exact ⟨.reeF4, m, rfl⟩
  | tits => exact ⟨.tits, rfl⟩

@[expose] def LieOuterRankFam (k : LieFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 3 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

theorem lieOuterRank_of_families (h : ∀ k, LieOuterRankFam k) : LieOuterRank := by
  intro S _ _ hS hnab idx hidx p hp hp2 D hD hcard
  obtain ⟨k, hk⟩ := exists_lieFamily idx.1
  exact h k S hS hnab idx hk hidx p hp hp2 D hD hcard

end CFSG.HardMathSupport.Timmesfeld.DefChar
