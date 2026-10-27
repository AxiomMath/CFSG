module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (CompOfType isL2three6)

@[expose] def I1430LieThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ^ 3 = 1 → α ≠ 1 → CompOfType S α isA6 → isL2three6 (.lie d)

@[expose] def I1430LieTwoInn : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∈ innAutDerived S → α ^ 3 = 1 → α ≠ 1 → CompOfType S α isA6 →
        ∃ ℓ : ℕ, 3 ≤ ℓ ∧ isBOfTwo ℓ (.lie d)

@[expose] def I1430LieTwoOut : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∉ innAutDerived S → α ^ 3 = 1 → CompOfType S α isA6 →
        isSp48 (.lie d)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
