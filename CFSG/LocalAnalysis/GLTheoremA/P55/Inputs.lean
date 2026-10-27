module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def oPPrimeP (p : ℕ) (X : Subgroup G) : Subgroup G :=
  ((CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).comap
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype

@[expose] def I336UsedAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ T D : Subgroup G,
    IsPGroup 2 T → IsElemAbelian p D → D ≤ Subgroup.normalizer (T : Set G) →
    (⁅T, D⁆ : Subgroup G) ≠ ⊥ →
    (∀ D₀ : Subgroup G, D₀ ≤ D → Nat.card D₀ * p = Nat.card D →
      (⁅T ⊓ Subgroup.centralizer (D₀ : Set G), D⁆ : Subgroup G) ≠ ⊥ →
      ∀ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer (D₀ : Set G) → IsElemAbelian 2 U →
        Nat.card U ≤ 2) →
    p = 3 ∧ (Nonempty (T ≃* QuaternionGroup 2) ∨ ∃ E : Subgroup G, E ≤ D ∧
      Nat.card E * 9 = Nat.card D ∧
      (⁅T ⊓ Subgroup.centralizer (E : Set G), D⁆ : Subgroup G) ≠ ⊥ ∧
      ∃ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer (E : Set G) ∧ IsElemAbelian 2 U ∧
        Nat.card U = 8)

@[expose] def DihedralUsed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (P U : Subgroup G) (k : ℕ),
    IsPGroup p P → IsElemAbelian 2 U → Nat.card U = 2 ^ (k + 1) →
    U ≤ Subgroup.normalizer (P : Set G) →
    (∀ u ∈ U, P ≤ Subgroup.centralizer ({u} : Set G) → u = 1) →
    ∃ u ∈ U, u ≠ 1 ∧ ∃ Q₁ : Subgroup G, Q₁ ≤ P ∧ IsElemAbelian p Q₁ ∧ Nat.card Q₁ = p ^ k ∧
      Q₁ ≤ Subgroup.centralizer ({u} : Set G) ∧ (⁅Q₁, U⁆ : Subgroup G) = Q₁

variable [Finite G]

@[expose] def I71UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (J S : Subgroup G), GLAIsBmax p B → IsEssential p B x →
    GLAPComponent p (Subgroup.centralizer ({x} : Set G)) J →
    B ≤ Subgroup.normalizer (J : Set G) → IsPGroup 2 S →
    S ≤ Subgroup.centralizer ({x} : Set G) → S ≤ Subgroup.normalizer (J : Set G) →
    B ≤ Subgroup.normalizer (S : Set G) → (⁅S, B⁆ : Subgroup G) = S →
    ∀ s ∈ S, InducesInnerMod p J s

@[expose] def I2611UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (J : Subgroup G), GLAIsBmax p B → IsEssential p B x →
    GLAPComponent p (Subgroup.centralizer ({x} : Set G)) J →
    B ≤ Subgroup.normalizer (J : Set G) → Odd (Nat.card (GLAPPrimeCoreOf p J)) →
    (∃ T : Subgroup G, T ≤ J ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥) →
    IsCyclic (Subgroup.center (PQuot p J)) → 4 ≤ GLATwoLocalRank p G →
    IsGB p B J ∨ ∃ A : Subgroup G, GLAIsBmax p A ∧ A ≤ J ⊔ B ∧
      (∃ U : Subgroup G, U ≤ J ⊔ B ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        A ≤ Subgroup.normalizer (U : Set G)) ∧
      (∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ J, a = u * v) ∧
      ¬ (A ⊓ J ≤ Subgroup.zpowers x)

@[expose] def I64UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (J : Subgroup G), GLAIsBmax p B → IsEssential p B x →
    GLAPComponent p (Subgroup.centralizer ({x} : Set G)) J →
    B ≤ Subgroup.normalizer (J : Set G) → ¬ IsCyclic (Subgroup.center (PQuot p J)) →
    ∀ b ∈ B, InducesInnerMod p J b

end CFSG.LocalAnalysis.GLTheoremA
