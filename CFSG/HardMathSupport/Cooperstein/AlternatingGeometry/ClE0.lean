module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.EOffender
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
open scoped commutatorElement

@[expose] def HY {G : Type} [Group G] (S L : Subgroup G) : Prop :=
  ∀ y ∈ ⁅S, S⁆ ⊔ Subgroup.closure {s ^ 2 | s ∈ S}, y ^ 2 = 1 → y ∈ blockV S L

@[expose] def E0Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Asc81bHyp X S → IsWeakSBlock X S L →
    S ≤ Subgroup.normalizer (L : Set G) → ∀ N : ℕ, 10 ≤ N →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin N), NaturalSectionTheta S L N θ →
    (∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S) → EOffenderData S (blockV S L) →
    (S.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ →
    ∀ Δ₀ : Finset (Fin N), Δ₀.card = 4 →
    ∀ P : Subgroup (Perm (Fin N)), Nat.card P = 4 → (∀ p ∈ P, p * p = 1) →
    (∀ p ∈ P, ∀ i, i ∉ Δ₀ → p i = i) → (∀ i ∈ Δ₀, ∀ j ∈ Δ₀, ∃ p ∈ P, p i = j) →
    ∀ ω : Perm (Fin N), (∀ x, ω (ω x) = x) → (∀ x ∈ Δ₀, ω x = x) → (∀ x, x ∉ Δ₀ → ω x ≠ x) →
    (S.subgroupOf (L ⊔ S)).map θ = P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)} →
    HY S L → False

@[expose] def E0NotYStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Asc81bHyp X S → IsWeakSBlock X S L →
    S ≤ Subgroup.normalizer (L : Set G) → ∀ N : ℕ, 10 ≤ N →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin N), NaturalSectionTheta S L N θ →
    (∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S) → EOffenderData S (blockV S L) →
    (S.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ →
    ∀ Δ₀ : Finset (Fin N), Δ₀.card = 4 →
    ∀ P : Subgroup (Perm (Fin N)), Nat.card P = 4 → (∀ p ∈ P, p * p = 1) →
    (∀ p ∈ P, ∀ i, i ∉ Δ₀ → p i = i) → (∀ i ∈ Δ₀, ∀ j ∈ Δ₀, ∃ p ∈ P, p i = j) →
    ∀ ω : Perm (Fin N), (∀ x, ω (ω x) = x) → (∀ x ∈ Δ₀, ω x = x) → (∀ x, x ∉ Δ₀ → ω x ≠ x) →
    (S.subgroupOf (L ⊔ S)).map θ = P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)} →
    ¬ HY S L → False

@[expose] def E0NonShortNotYStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Asc81bHyp X S → IsWeakSBlock X S L →
    S ≤ Subgroup.normalizer (L : Set G) → ∀ N : ℕ, 10 ≤ N →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin N), NaturalSectionTheta S L N θ →
    (∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S) → EOffenderData S (blockV S L) →
    (S.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ →
    ∀ Δ₀ : Finset (Fin N), Δ₀.card = 4 →
    ∀ P : Subgroup (Perm (Fin N)), Nat.card P = 4 → (∀ p ∈ P, p * p = 1) →
    (∀ p ∈ P, ∀ i, i ∉ Δ₀ → p i = i) → (∀ i ∈ Δ₀, ∀ j ∈ Δ₀, ∃ p ∈ P, p i = j) →
    ∀ ω : Perm (Fin N), (∀ x, ω (ω x) = x) → (∀ x ∈ Δ₀, ω x = x) → (∀ x, x ∉ Δ₀ → ω x ≠ x) →
    (S.subgroupOf (L ⊔ S)).map θ = P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)} →
    ¬ HY S L → ¬ ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L → False

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
