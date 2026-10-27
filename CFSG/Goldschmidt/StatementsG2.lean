module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG
public import CFSG.Walter.Bender1970.S3.Setup

public section

namespace CFSG.Goldschmidt

open CFSG.Open

@[expose] def S_G51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a,
    UniquenessA a H ∨
      (a ∈ GorensteinWalter.qCoreOf H 2 ∧
        ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (GorensteinWalter.qCoreOf H p) ≤ 2)

@[expose] def S_G52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ Y : Subgroup G, Y ≠ ⊥ →
    Y ≤ GorensteinWalter.generalizedFittingSubgroupOf H →
    (Y.subgroupOf (GorensteinWalter.generalizedFittingSubgroupOf H)).IsSubnormal →
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Y : Set G) → Y ∈ goldA a H

@[expose] def S_G53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ Y V : Subgroup G, Y ≠ ⊥ →
    Y ≤ GorensteinWalter.generalizedFittingSubgroupOf H →
    (Y.subgroupOf (GorensteinWalter.generalizedFittingSubgroupOf H)).IsSubnormal →
    a ∈ Subgroup.normalizer (Y : Set G) →
    V ≤ GorensteinWalter.generalizedFittingSubgroupOf H →
    (V.subgroupOf (GorensteinWalter.generalizedFittingSubgroupOf H)).IsSubnormal →
    a ∈ Subgroup.normalizer (V : Set G) → V ≤ Subgroup.normalizer (Y : Set G) →
    ((⁅V, Subgroup.zpowers a⁆ = V ∧ V ∈ goldA a H) ∨
      (⁅V, Subgroup.zpowers a⁆ = ⊥ ∧
        (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p V ∧ Nat.card V = p ^ 2) ∧
        ∀ v ∈ V, v ≠ 1 → Subgroup.zpowers v ∈ goldA a H)) →
    Y ∈ goldA a H

@[expose] def S_G54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ p : ℕ, p.Prime → p ≠ 2 →
    ⁅GorensteinWalter.qCoreOf H p, Subgroup.zpowers a⁆ ≠ ⊥ →
    GorensteinWalter.qCoreOf H p ⊓ Subgroup.centralizer ({a} : Set G) ≤
      GorensteinWalter.qCoreOf H p ⊓
        Subgroup.centralizer (GorensteinWalter.qCoreOf H p : Set G) →
    IsCyclic (GorensteinWalter.qCoreOf H p ⊓
      Subgroup.centralizer (GorensteinWalter.qCoreOf H p : Set G) : Subgroup G) →
    IsPGroup p (GorensteinWalter.generalizedFittingSubgroupOf H)

@[expose] def S_G55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, a ∉ GorensteinWalter.qCoreOf H 2 →
    UniquenessA a H

@[expose] def S_G56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a,
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 ≤ CFSG.Open.pRank p (GorensteinWalter.qCoreOf H p)) →
    UniquenessA a H

@[expose] def S_G61 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ A₁ : Subgroup G, A₁ ≤ A →
    (A₁.subgroupOf A).index = 2 → (∀ a₁ ∈ A₁, a₁ ≠ 1 → CFSG.Walter.benderM a₁ = {H}) →
    Nat.card A = 4 ∧ A₁ = Subgroup.zpowers a

@[expose] def S_G62 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ p : ℕ, p.Prime → p ≠ 2 →
    ¬ IsPGroup p (GorensteinWalter.generalizedFittingSubgroupOf H)

@[expose] def S_G63 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ p : ℕ, p.Prime → p ≠ 2 →
    (⁅GorensteinWalter.qCoreOf H p, Subgroup.zpowers a⁆ ≠ ⊥ ∨
      3 ≤ CFSG.Open.pRank p (GorensteinWalter.qCoreOf H p)) →
    ∀ a₁ ∈ A, a₁ ≠ 1 → ∀ H₁ ∈ CFSG.Walter.benderM a₁, H₁ ≠ H →
    GorensteinWalter.qCoreOf (fstarZero H) p ⊓ H₁ ≠ ⊥ →
    (GorensteinWalter.qCoreOf (fstarZero H) p ⊓ H₁ ⊓ GorensteinWalter.qCoreOf H₁ p = ⊥ ∧
      ⁅GorensteinWalter.qCoreOf (fstarZero H) p ⊓ H₁, Subgroup.zpowers a⁆ = ⊥) ∧
    IsCyclic (GorensteinWalter.qCoreOf (fstarZero H) p ⊓ H₁ : Subgroup G)

@[expose] def S_G64 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a,
    a ∈ GorensteinWalter.generalizedFittingSubgroupOf H ∧
      ((∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (GorensteinWalter.qCoreOf H p) ≤ 2) ∨
        Nat.card A = 4)

end CFSG.Goldschmidt
