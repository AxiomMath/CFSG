module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

@[expose] def HeldEndSetting (X : Type) [Group X] [Finite X] (L : Subgroup X) : Prop :=
  HeldSetting X L ∧
    (∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥) ∧
    IsStandardSubgroup L ∧ Nonempty (L ≃* Blueprint.NativeSporadic.He) ∧
    pRank 2 ↥(centralizer (L : Set X)) = 1

@[expose] def HeldTwoA {X : Type} [Group X] (L : Subgroup X) (w : X) : Prop :=
  w ∈ L ∧ orderOf w = 2 ∧ gsFixedLayer L w ≠ ⊥

@[expose] def HeldKNormalStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L →
    ∀ u : X, HeldTwoA L u →
      ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).Normal ∧
      ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({u} : Set X) →
        (K₁.subgroupOf (centralizer ({u} : Set X))).Normal →
        Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u)) → K₁ = gsFixedLayer L u

@[expose] def HeldZStarEndStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L →
    (∀ u : X, HeldTwoA L u →
      ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).Normal ∧
      ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({u} : Set X) →
        (K₁.subgroupOf (centralizer ({u} : Set X))).Normal →
        Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u)) → K₁ = gsFixedLayer L u) →
    (∀ v ∈ L, orderOf v = 2 → ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({v} : Set X) →
      (K₁.subgroupOf (centralizer ({v} : Set X))).Normal →
      (∃ u : X, HeldTwoA L u ∧ Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u))) → HeldTwoA L v) →
    (∀ u : X, HeldTwoA L u → centralizer ({u} : Set X) ≤ normalizer (L : Set X)) →
    False

@[expose] def HeldTwoBCentralizerFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) →
    ∀ v ∈ L, orderOf v = 2 → gsFixedLayer L v = ⊥ →
      ⁅L ⊓ centralizer ({v} : Set X), L ⊓ centralizer ({v} : Set X)⁆ =
        L ⊓ centralizer ({v} : Set X) ∧
      ∃ x ∈ L ⊓ centralizer ({v} : Set X), x ^ 12 = 1 ∧
        ∃ w₁ ∈ L ⊓ centralizer ({v} : Set X), ∃ w₂ ∈ L ⊓ centralizer ({v} : Set X),
          HeldTwoA L w₁ ∧ HeldTwoA L w₂ ∧
          (∀ N : Subgroup X, N ≤ L ⊓ centralizer ({v} : Set X) →
            (N.subgroupOf (L ⊓ centralizer ({v} : Set X))).Normal → (x ^ 4 ∈ N ∨ x ^ 3 ∈ N) →
            w₁ ∈ N ∧ w₂ ∈ N) ∧
          v ∉ centralizer (gsFixedLayer L w₁ : Set X) ∧
          v ∉ centralizer (gsFixedLayer L w₂ : Set X) ∧
          gsFixedLayer L w₁ ⊔ gsFixedLayer L w₂ = L

@[expose] def HeldTwoALayerFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) → ∀ u : X, HeldTwoA L u →
      ⁅gsFixedLayer L u, gsFixedLayer L u⁆ = gsFixedLayer L u ∧
      IsL34Type (↥(gsFixedLayer L u) ⧸ center ↥(gsFixedLayer L u))

@[expose] def HeldTwoAFourFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) → ∀ u : X, HeldTwoA L u →
      ∃ y₁ ∈ gsFixedLayer L u, ∃ y₂ ∈ gsFixedLayer L u, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧
        y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧ y₁ * y₂ = y₂ * y₁

@[expose] def HeldTwoAClassFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) → ∀ u w : X, HeldTwoA L u → HeldTwoA L w →
      ∃ l ∈ L, w = l * u * l⁻¹

@[expose] def HeldTwoAPairFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) → ∀ u : X, HeldTwoA L u →
      ∃ w ∈ gsFixedLayer L u, HeldTwoA L w ∧
        w ∉ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype ∧
        u * w ∉ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype

@[expose] def HeldTwoAGenerationFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) → ∀ u w : X, HeldTwoA L u → HeldTwoA L w →
      w ∈ gsFixedLayer L u →
      w ∉ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype →
      u * w ∉ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype →
      gsFixedLayer L u ⊔ gsFixedLayer L w = L

end CFSG.ComponentClassification.GrSLit
