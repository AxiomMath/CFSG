module

public import CFSG.GH74.GLS.Balance.Bender.OpStarBasic

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def BenderL52i (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.Coprime p (Nat.card Y) → IsPStar p Y

@[expose] def BenderL52ii (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal], IsPStar p Y → IsPStar p (Y ⧸ N)

@[expose] def BenderL52iii (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H), K.Normal → K ≠ ⊥ →
    (∀ M : Subgroup H, M ≤ K → M.Normal → M = ⊥ ∨ M = K) → IsPStar p ↥(oResidual p ↥K)

@[expose] def BenderL52iv (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsPStar p Y → ∀ P : Subgroup Y, P.Normal → IsPGroup p ↥P →
    P ≤ center Y

@[expose] def BenderQ42iii (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (X A N : Subgroup H) [N.Normal], A ≤ normalizer (X : Set H) →
    IsPGroup p ↥A → N ≤ X → (∀ n ∈ N, ∀ x ∈ X, n * x = x * n) →
      oResOf p (X.map (QuotientGroup.mk' N) ⊓ centralizer ((A.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) :
          Set (H ⧸ N))) = (oResOf p (X ⊓ centralizer (A : Set H))).map (QuotientGroup.mk' N)

@[expose] def BenderQ43iii (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y A : Subgroup G), IsPGroup p ↥A → A ≤ normalizer (Y : Set G) →
    Nat.Coprime p (Nat.card Y) → Y = ⁅Y, A⁆ ⊔ (Y ⊓ centralizer (A : Set G))

@[expose] def BenderQ326 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N A : Subgroup H), N.Normal → N ≠ ⊥ →
    (∀ M : Subgroup H, M ≤ N → M.Normal → M = ⊥ ∨ M = N) → (∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) →
      N ≤ ⁅N, A⁆ ⊔ (N ⊓ centralizer (A : Set H))

@[expose] def BenderL53 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X N P : Subgroup G) [(N.subgroupOf X).Normal],
    N ≤ X → IsSylowIn p P N → IsPStar p (↥X ⧸ N.subgroupOf X) → IsPStar p ↥(oResOf p N) →
      oResOf p X ≤ oResOf p N ⊔ (X ⊓ centralizer (P : Set G)) → IsPStar p ↥(oResOf p X)

@[expose] def BenderL54 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X N P : Subgroup G),
    IsPStar p ↥X → N ≤ X → (N.subgroupOf X).Normal → IsSylowIn p P N →
      IsPStar p ↥(oResOf p (X ⊓ centralizer (P : Set G)))

@[expose] def BenderL55 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P : Subgroup G),
    IsPStar p ↥X → IsPGroup p ↥P → P ≤ normalizer (X : Set G) →
      X = ⁅X, P⁆ ⊔ oResOf p (X ⊓ centralizer (P : Set G))

@[expose] def BenderL56 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X N₁ N₂ : Subgroup G),
    N₁ ≤ X → N₂ ≤ X → (N₁.subgroupOf X).Normal → (N₂.subgroupOf X).Normal →
      IsPStar p ↥N₁ → IsPStar p ↥N₂ → IsPStar p ↥(N₁ ⊔ N₂)

@[expose] def BenderT59 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P : Subgroup G),
    IsSylowIn p P (OpStarP p X) → X ⊓ centralizer (P : Set G) ≤ OpStarP p X

@[expose] def BenderT510 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P : Subgroup G),
    IsPStar p ↥X → IsPGroup p ↥P → P ≤ normalizer (X : Set G) →
      X = ⁅X, P⁆ ⊔ OpStar p (X ⊓ centralizer (P : Set G))

@[expose] def BenderT511 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P : Subgroup G), IsPGroup p ↥P → P ≤ normalizer (X : Set G) →
    OpStar p (X ⊓ centralizer (P : Set G)) ≤ OpStar p X

end CFSG.GH74.GLS.Balance
