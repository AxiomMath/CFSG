module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.Basic

public section

namespace CFSG.Goldschmidt

open CFSG.Open

@[expose] def S_lemmaX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → ∀ (S : Sylow 2 G) (A U : Subgroup G), A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A → IsElemAbelian 2 U → U ≠ ⊥ →
    fusionStronglyClosed (U : Set G) (S : Subgroup G) →
    (8 ≤ Nat.card U ∨ U ≤ Subgroup.centralizer ((S : Subgroup G) : Set G)) →
    ∀ H : Subgroup G, H ≠ ⊤ → Subgroup.normalizer (U : Set G) ≤ H →
    (∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H) →
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder H

@[expose] def S_corX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → ∀ (S : Sylow 2 G) (A U : Subgroup G), A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → 8 ≤ Nat.card U →
    (∀ w ∈ U, w ≠ 1 → let M := normalClosureIn (Subgroup.centralizer ({w} : Set G)) U
      goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊥) →
    ∃ H : Subgroup G, CFSG.BenderSuzuki.IsStronglyEmbeddedOrder H

@[expose] def S_caseZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → CFSG.Assembly.IsComponentType G → 3 ≤ CFSG.Assembly.twoRank G →
    (∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) →
    ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G) →
    ∀ A U : Subgroup G, A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → 8 ≤ Nat.card U →
    (∃ u ∈ U, u ≠ 1 ∧
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (U : Set G)) →
    False

@[expose] def S_HC1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → CFSG.Assembly.IsComponentType G → 3 ≤ CFSG.Assembly.twoRank G →
    (∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) →
    ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G) →
    ∀ A U : Subgroup G, A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → 8 ≤ Nat.card U →
    (∃ u ∈ U, u ≠ 1 ∧ let M := normalClosureIn (Subgroup.centralizer ({u} : Set G)) U
      goldschmidtLayer (M ⧸ goldschmidtOddCore M) ≠ ⊥) →
    (∀ u ∈ U, u ≠ 1 →
      ¬ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (U : Set G)) →
    ∃ H : Subgroup G, H ≠ ⊤ ∧ Subgroup.normalizer (U : Set G) ≤ H ∧
      ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H

@[expose] def S_HC2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → CFSG.Assembly.IsComponentType G → 3 ≤ CFSG.Assembly.twoRank G →
    (∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) →
    ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G) →
    ∀ A U : Subgroup G, A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → Nat.card U = 4 → ¬ fusionIsTI U →
    ∃ H : Subgroup G, H ≠ ⊤ ∧ Subgroup.normalizer (U : Set G) ≤ H ∧
      ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H

end CFSG.Goldschmidt
