module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def L6_2 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
        ∀ J ∈ Ω, J ∉ twinSet Ω K → ∀ t : G, IsUniqueInvolution J t →
          ∀ V : Subgroup G, IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G)) → t ∈ V →
            (V = Subgroup.zpowers t ∧ conjSub t K ≠ K) ∨
            (V = Subgroup.zpowers t ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
              ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
                IsSemidihedral (R ⊔ V)) ∨
            (V ∈ USet Ω ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
              ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
                IsWreathed (R ⊔ V)) ∨
            (V ∈ RSet Ω ∧ ⁅V, K⁆ ≤ oddCoreOf K)

@[expose] def L6_3 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ K ∈ Ω, ∀ L ∈ twinSet Ω K,
        KPerp Ω K = KPerp Ω L ∧
          omegaStarNbr Ω K \ omegaNbr Ω K = omegaStarNbr Ω L \ omegaNbr Ω L

@[expose] def L6_5 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ Δ : Set (Subgroup G), Δ ⊆ RSet Ω →
        (∀ R ∈ Δ, ∀ R' ∈ Δ, R ≠ R' → Commutes R R') →
          ∀ R ∈ Δ, (R ⊔ ⨆ R' ∈ Δ, centerIn R') ⊓
            ((⨆ R' ∈ Δ, centerIn R') ⊔ ⨆ R' ∈ Δ, ⨆ (_ : R' ≠ R), R') = ⨆ R' ∈ Δ, centerIn R'

@[expose] def L6_6 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ S : Subgroup G, IsPGroup 2 S → ∀ Δ : Set (Subgroup G), (∀ A ∈ Δ, A ≤ S) →
        (∀ A ∈ Δ, ∀ s ∈ S, conjSub s A ∈ Δ) →
          (Δ ⊆ RSet Ω ∨
            ((∀ A ∈ Δ, IsCyclic ↥A ∧ 4 ≤ Nat.card ↥A) ∧
              ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ∃ J ∈ Ω, ∃ J' ∈ Ω, J ≠ J' ∧ A ≤ J ∧ B ≤ J')) →
            ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B

@[expose] def L6_7 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ S : Sylow 2 G, ∀ R ∈ RSet Ω, ∀ R' ∈ RSet Ω, R ≤ (S : Subgroup G) →
        R' ≤ (S : Subgroup G) → R ≠ R' → Commutes R R'

@[expose] def L6_8 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ S : Sylow 2 G, ∀ U ∈ USet Ω, U ≤ (S : Subgroup G) → ∀ η ∈ etaG Ω,
        (∀ V ∈ η, V ≤ (S : Subgroup G)) →
          ∃! V : Subgroup G, V ∈ η ∧ (U = V ∨ (U ⊔ V) ∈ RSet Ω)

@[expose] def L6_9 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ S : Sylow 2 G,
        (∃ η ∈ etaSet Ω (S : Subgroup G), ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧
        ∀ η ∈ etaSet Ω (S : Subgroup G), (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) →
          (∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x) ∧
            {U | U ∈ USet Ω ∧ U ≤ ⨆ V ∈ η, V} = η

@[expose] def L6_10 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
        (∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → ∀ r ∈ R, ∀ V ∈ η, conjSub r V ∈ η) ∧
        (∀ U ∈ USet Ω, U ≤ (S : Subgroup G) → ∀ u ∈ U, ∀ V ∈ η, conjSub u V ∈ η)

@[expose] def L6_11 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
        ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (⨆ V ∈ η, V) ∈ η

@[expose] def L6_13 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ R ∈ RSet Ω, ∀ Y X : Subgroup G, R ≤ Y → X ≤ Y → (∀ y ∈ Y, conjSub y X = X) →
        R ⊓ X = ⊥ →
          (⨆ R' ∈ {R' : Subgroup G | (∃ y ∈ Y, R' = conjSub y R) ∧ R' ≤ R ⊔ X}, R') ≤
              R ⊔ oddCoreOf X ∧
            ⁅R, X⁆ ≤ oddCoreOf X

end CFSG.ClassicalInvolution.Asc77
