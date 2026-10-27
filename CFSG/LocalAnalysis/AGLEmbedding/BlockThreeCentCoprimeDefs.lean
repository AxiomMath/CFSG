module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.AGLEmbedding

@[expose] def ThreeAutFixedTwoThree (X : Type*) [Group X] : Prop :=
  ∀ α : MulAut X, α ^ 3 = 1 →
    (∀ Q : Subgroup X, ⁅Q, Q⁆ = Q → (∀ y ∈ Q, α y = y) → Q = ⊥) →
    ∀ x : X, x⁻¹ * α x ∈ Subgroup.center X → ∀ n : ℕ, Nat.Coprime 6 n →
      x ^ n ∈ Subgroup.center X → x ∈ Subgroup.center X

@[expose] def IsThreeCentLieIndex : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => q.card = 2 ∨ (r = 2 ∧ q.card = 3)
  | .B _ q | .D _ q | .twistedD _ q => q.card = 2
  | _ => False

@[expose] def KFactThreeCentLieTwo : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsThreeCentLieIndex d.1 →
    ThreeAutFixedTwoThree (TauCeti.CFSGIndex.lie d).Group

end CFSG.AGLEmbedding
