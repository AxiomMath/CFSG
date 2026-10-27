module

public import CFSG.Open.SQTKSimpleListTauCeti

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Assembly CFSG.Open.SQTKTauCeti

@[expose] def IsSQTKSporadicName (s : TauCeti.SporadicName) : Prop :=
  s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
    s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru

instance (s : TauCeti.SporadicName) : Decidable (IsSQTKSporadicName s) := by
  unfold IsSQTKSporadicName; infer_instance

@[expose] def TCExcludedSporadic (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Nonempty (G ≃* s.Group) →
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧
      ∃ E : Subgroup G, CFSG.Open.IsElemAbelian ℓ E ∧ Nat.card E = ℓ ^ 3

@[expose] def TCLieCase (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    StronglyQuasithin G → Nonempty (G ≃* d.Group) → SQTKSimpleList G

end CFSG.QuasithinUnique.SQTK
