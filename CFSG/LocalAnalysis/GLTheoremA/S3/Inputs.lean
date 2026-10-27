module

public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def KMUsedAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ A T : Subgroup G,
    IsElemAbelian p A → IsPGroup 2 T → A ≤ Subgroup.normalizer (T : Set G) →
    (∀ a ∈ A, (∀ t ∈ T, a * t = t * a) → a = 1) → p ^ 3 ≤ Nat.card A →
    (∀ E : Subgroup G, E ≤ A → ∀ k : ℕ, k ≤ 2 → Nat.card E * p ^ k = Nat.card A →
      ∀ V : Subgroup G, V ≤ T ⊓ Subgroup.centralizer (E : Set G) → IsElemAbelian 2 V →
        Nat.card V ≤ 2 ^ (k + 1)) →
    GLASymplecticType T ∧ p = 3

@[expose] def I1135At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (B : Subgroup G) (y : G) (K : Subgroup G),
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({y} : Set G)) → GLAIsBmax p B →
    IsEssential p B y → GLAPComponent p (Subgroup.centralizer ({y} : Set G)) K →
    ¬ B ≤ Subgroup.normalizer (K : Set G) → IsChevSimple p (PSimple p K) → IsSC p B

@[expose] def ChevClosureAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K A : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
    IsChevSimple p (PSimple p K) → IsElemAbelian p A → A ≤ Subgroup.normalizer (K : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J →
      IsChevSimple p (PSimple p J)

@[expose] def ChevUniqueAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K A : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
    IsChevSimple p (PSimple p K) → IsElemAbelian p A → A ≤ Subgroup.normalizer (K : Set G) →
    ∀ J J' : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J →
      GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J' → J = J'

@[expose] def ChevInnerAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K A : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
    IsChevSimple p (PSimple p K) → IsElemAbelian p A → A ≤ Subgroup.normalizer (K : Set G) →
    (∃ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J) →
    ∀ a ∈ A, CentMod p K a ∨ ¬ InducesInnerMod p K a

@[expose] def I65At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
    IsChevSimple p (PSimple p K) →
    (∃ a ∈ Subgroup.normalizer (K : Set G), a ^ p = 1 ∧ ¬ CentMod p K a ∧
      ¬ InducesInnerMod p K a) → Subgroup.center (PQuot p K) = ⊥

@[expose] def I76At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K A : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
    IsChevSimple p (PSimple p K) → IsElemAbelian p A → A ≤ Subgroup.normalizer (K : Set G) →
    (∀ a ∈ A, ¬ CentMod p K a → ¬ InducesInnerMod p K a) →
    Nat.card A ≤ p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ∧
      (Nat.card A = p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) →
        p = 3 ∧ 12 ≤ GLATwoLocalRank p (PQuot p K))

@[expose] def ChevRank3At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
    IsChevSimple p (PSimple p K) → GLATwoLocalRank p (PQuot p K) ≤ 3 → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (K : Set G) →
    Nat.card B = p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p K) →
    (∃ b ∈ B, ¬ CentMod p K b ∧ ¬ InducesInnerMod p K b) →
    (∃ P : Subgroup G, P ≤ K ∧ IsElemAbelian p P ∧ Nat.card P = p ^ 6) ∧
    (∀ T : Subgroup G, IsPGroup 2 T → T ≤ Subgroup.normalizer (K : Set G) →
      B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = T →
      ∀ t ∈ T, CentMod p K t)

@[expose] def I112L227At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X B L : Subgroup G), CFSG.Open.IsKGroup ↥X → B ≤ X → IsElemAbelian 3 B →
    GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B → GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) (onLie (isL2 27)) → B ≤ Subgroup.normalizer (L : Set G)

@[expose] def L227DataAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    catalogIs (PSimple 3 K) (onLie (isL2 27)) →
    Subgroup.center (PQuot 3 K) = ⊥ ∧
    (∃ P : Subgroup (PQuot 3 K), IsElemAbelian 3 P ∧ Nat.card P = 27) ∧
    ∀ A : Subgroup G, IsElemAbelian 3 A → A ≤ Subgroup.normalizer (K : Set G) →
      (∃ a ∈ A, ¬ InducesInnerMod 3 K a) →
      Nat.card A ≤ 9 * Nat.card ↥(A ⊓ centModSubgroup 3 K)

@[expose] def L227PumpAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (Y K J : Subgroup G) (b x : G), CFSG.Open.IsKGroup ↥Y → GLAPComponent 3 Y K →
    b ∈ Subgroup.normalizer (K : Set G) → b ^ 3 = 1 → x ∈ Subgroup.normalizer (K : Set G) →
    x ∈ Subgroup.normalizer (J : Set G) → x ^ 3 = 1 → b * x = x * b →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J →
    catalogIs (PSimple 3 J) (onLie (isL2 27)) → ¬ InducesInnerMod 3 J x → CentMod 3 K b

end CFSG.LocalAnalysis.GLTheoremA
