module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def JStarResidualD4TwoThree : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .trialityD4 q → Nonempty (L ≃* CatGroup d) →
    ¬ JStarElimData L 3 3

@[expose] def JStarResidualSp48Three : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    ∀ (d : TauCeti.ValidLieTypeIndex), IsSpFourEightIndex d →
    Nonempty (L ≃* CatGroup d) → ¬ JStarElimData L 3 3

@[expose] def JStarResidualE6TwoSix : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .E6 q → Nonempty (L ≃* CatGroup d) →
    ¬ JStarElimData L 3 6

@[expose] def JStarResidualE6TwoTwo : Prop :=
  ∀ (d₀ : TauCeti.ValidLieTypeIndex), IsUnitaryIndex 3 d₀ → d₀.1.fieldExponent = 2 →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
      q.p = 2 → q.exponent = 1 → d.1 = .E6 q → Nonempty (L ≃* CatGroup d) →
      ¬ JStarElimDataOf L 3 (3 ^ (3 * d₀.1.fieldExponent) * d₀.1.fieldExponent) (CatGroup d₀)

@[expose] def D4TwoRankTwo : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .trialityD4 q → Nonempty (L ≃* CatGroup d) →
    ∀ E : Subgroup L, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2

@[expose] def E6TwoRankFour : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .E6 q → Nonempty (L ≃* CatGroup d) →
    ∀ E : Subgroup L, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 4

@[expose] def E6TwoHasOrderNine : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .E6 q → Nonempty (L ≃* CatGroup d) →
    ∃ g : L, orderOf g = 9

end CFSG.AGLEmbedding
