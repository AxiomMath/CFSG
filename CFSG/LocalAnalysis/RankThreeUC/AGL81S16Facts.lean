module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Conj

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure LocalSetting (p : ℕ) (M V : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  ne_bot : V ≠ ⊥
  normalizer_eq : normalizer (V : Set G) = M
  self_normalizing : normalizer (M : Set G) = M
  spe : ∀ g : G, g ∉ M → ¬ p ∣ Nat.card ↥(M ⊓ cj g M)
  u2 : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup 2 ↥X →
    2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (X : Set G)) → normalizer (X : Set G) ≤ M

structure U4LocalFacts (p n : ℕ) (M L V : Subgroup G) (sing : G → Prop) : Prop where
  card_V : Nat.card ↥V = 2 ^ (8 * n)
  nonsing_good : ∀ v ∈ V, v ≠ 1 → ¬ sing v →
    2 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G))
  p_dvd : ∀ v ∈ V, v ≠ 1 → p ∣ Nat.card ↥(M ⊓ centralizer ({v} : Set G))
  ts_index : ∀ W : Subgroup G, W ≤ V → (∀ w ∈ W, w ≠ 1 → sing w) →
    2 ^ (4 * n) ≤ W.relIndex V
  inv_index : ∀ t ∈ M, IsPGroup 2 ↥(zpowers t) → t ∉ centralizer (V : Set G) →
    2 ^ (2 * n) ≤ (V ⊓ centralizer ({t} : Set G)).relIndex V
  Q_le : ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A → ¬ A ≤ centralizer (V : Set G) →
    (∀ B : Subgroup G, B ≤ A → B.relIndex A < 2 ^ (2 * n) →
      V ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G)) →
    A ≤ L ⊔ (M ⊓ centralizer (V : Set G))
  dim_F : ∀ B : Subgroup G, B ≤ M → B ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
    ∃ j : ℕ, Nat.card ↥(V ⊓ centralizer (B : Set G)) = 2 ^ (2 * n * j)
  ts_plane : ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A →
    A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
    2 ^ (2 * n) ≤ (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A →
    (∀ u ∈ ⁅A, V⁆, u ≠ 1 → sing u) →
    ⁅A, V⁆ = V ⊓ centralizer (A : Set G) ∧ Nat.card ↥(⁅A, V⁆) = 2 ^ (4 * n)
  transvection : ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A →
    A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
    (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A = 2 ^ (4 * n) →
    (∀ u ∈ ⁅A, V⁆, u ≠ 1 → sing u) →
    ∃ B : Subgroup G, B ≤ A ∧ A ⊓ (M ⊓ centralizer (V : Set G)) ≤ B ∧
      Nat.card ↥B = 2 ^ n * Nat.card ↥(A ⊓ (M ⊓ centralizer (V : Set G))) ∧
      B = A ⊓ centralizer ((V ⊓ centralizer (B : Set G) : Subgroup G) : Set G)
  rank_le : ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A →
    A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
    (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A ≤ 2 ^ (4 * n)
  generation : ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A →
    A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
    (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A = 2 ^ (4 * n) →
    ∀ X : Subgroup G, (∀ a ∈ A, a ∉ M ⊓ centralizer (V : Set G) →
      V ⊓ centralizer ({a} : Set G) ≤ X) → V ≤ X

end CFSG.LocalAnalysis.RankThreeUC
