module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG
public import CFSG.Walter.Bender1970.S3.Setup

public section

namespace CFSG.Goldschmidt

open CFSG.Open

@[expose] def S_G71 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    8 ≤ Nat.card A → ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a,
    ∃ n : ℕ, (derivedSeries (normalClosureIn H A) n).map (normalClosureIn H A).subtype ≤
      GorensteinWalter.componentLayerOf (normalClosureIn H A)

@[expose] def S_G72 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → 3 ≤ CFSG.Assembly.twoRank G →
    (∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) →
    ∀ (S : Sylow 2 G) (A U : Subgroup G), A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → 8 ≤ Nat.card U →
    ∃ a ∈ U, a ≠ 1 ∧ ∃ H ∈ CFSG.Walter.benderM a,
      GorensteinWalter.componentLayerOf (normalClosureIn H U) ≠ ⊥

@[expose] def S_G73 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    8 ≤ Nat.card A → ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ K : Subgroup G,
    GorensteinWalter.IsComponentOf K (normalClosureIn H A) →
    (IsGoldL2 K → ∀ a' ∈ A, a' ≠ 1 → ∀ H' ∈ CFSG.Walter.benderM a', ∀ K' : Subgroup G,
      GorensteinWalter.IsComponentOf K' (normalClosureIn H' A) → IsGoldL2 K') →
    ∀ a₀ ∈ A ⊓ Subgroup.centralizer (K : Set G), a₀ ≠ 1 → CFSG.Walter.benderM a₀ = {H}

@[expose] def S_G74 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    8 ≤ Nat.card A →
    (∃ a ∈ A, a ≠ 1 ∧ ∃ H ∈ CFSG.Walter.benderM a,
      GorensteinWalter.componentLayerOf (normalClosureIn H A) ≠ ⊥) →
    ∃ a ∈ A, a ≠ 1 ∧ ∃ H ∈ CFSG.Walter.benderM a, ∃ K : Subgroup G,
      GorensteinWalter.IsComponentOf K (normalClosureIn H A) ∧
      (∀ a₀ ∈ A ⊓ Subgroup.centralizer (K : Set G), a₀ ≠ 1 →
        CFSG.Walter.benderM a₀ = {H}) ∧
      2 ≤ Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ∧
      Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ^ 2 ≤ Nat.card A ∧
      ¬ Subgroup.normalizer (A : Set G) ≤ H ∧
      ∀ g ∈ Subgroup.normalizer (A : Set G), g ∉ H →
        A ⊓ Subgroup.centralizer (K : Set G) ⊓
          conjSub g (A ⊓ Subgroup.centralizer (K : Set G)) = ⊥

@[expose] def S_G75 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    8 ≤ Nat.card A →
    (∃ a ∈ A, a ≠ 1 ∧ ∃ H ∈ CFSG.Walter.benderM a,
      GorensteinWalter.componentLayerOf (normalClosureIn H A) ≠ ⊥) →
    Nat.card A = 8 ∧
      ((Subgroup.centralizer (A : Set G)).subgroupOf (Subgroup.normalizer (A : Set G))).index =
        21 ∧
      ∃ x ∈ Subgroup.normalizer (A : Set G), ∃ y ∈ Subgroup.normalizer (A : Set G),
        x * y * x⁻¹ * y⁻¹ ∉ Subgroup.centralizer (A : Set G)

@[expose] def S_G76 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    8 ≤ Nat.card A →
    (∃ a ∈ A, a ≠ 1 ∧ ∃ H ∈ CFSG.Walter.benderM a,
      GorensteinWalter.componentLayerOf (normalClosureIn H A) ≠ ⊥) →
    CFSG.Walter.IsTypeJR G

@[expose] def S_G81 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    Nat.card A = 4 → ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a,
    H = Subgroup.centralizer ({a} : Set G) ∧
      H = oddCoreOf H ⊔ Subgroup.centralizer (A : Set G) ∧ ⁅A, oddCoreOf H⁆ ≠ ⊥ ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ V : Subgroup G, V ≤ CFSG.fittingSubgroupOf H →
        IsPGroup p V → ¬ IsCyclic V →
        (∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H) →
        ∀ M : Subgroup G, IsCoatom M → Subgroup.zpowers a ⊔ V ≤ M → M = H

@[expose] def S_G82 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    Nat.card A = 4 → ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ p : ℕ, p.Prime →
    GorensteinWalter.qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥ →
    ∀ M : Subgroup G, IsCoatom M →
    Subgroup.normalizer
        ((GorensteinWalter.qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :
          Set G) ≤ M →
    M ≠ H → a ∉ GorensteinWalter.generalizedFittingSubgroupOf M

@[expose] def S_G83 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    Nat.card A = 4 → ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a,
    (∀ a₁ ∈ A, a₁ ≠ 1 → ∀ p : ℕ, p.Prime →
      (∀ x ∈ GorensteinWalter.qCoreOf H p, a₁⁻¹ * x * a₁ = x) ∨
        ∀ x ∈ GorensteinWalter.qCoreOf H p, a₁⁻¹ * x * a₁ = x⁻¹) ∧
    ⁅GorensteinWalter.componentLayerOf H, A⁆ = ⊥

@[expose] def S_G84 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    Nat.card A = 4 → ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ V : Subgroup G,
    V ≤ CFSG.fittingSubgroupOf H → (Nat.card V).Prime → Subgroup.normalizer (V : Set G) ≤ H

@[expose] def S_G86 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    Nat.card A = 4 → ¬ IsMulCommutative (S : Subgroup G) →
    ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a,
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (∀ b ∈ A, b ∉ Subgroup.zpowers a → ∀ x ∈ GorensteinWalter.qCoreOf H p,
        b⁻¹ * x * b = x⁻¹) ∧
      CFSG.Open.pRank p (GorensteinWalter.qCoreOf H p) = 2 ∧
      ∀ t ∈ H ⊓ Subgroup.centralizer (GorensteinWalter.qCoreOf H p : Set G),
        t ^ 2 = 1 → t = 1 ∨ t = a

@[expose] def S_G87 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    Nat.card A = 4 → ¬ IsMulCommutative (S : Subgroup G) →
    CFSG.Open.pRank 2 (S : Subgroup G) = 3 ∧
      IsMulCommutative (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G) ∧
      Nat.card (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G) =
        Monoid.exponent (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G) ^ 2 ∧
      A = Omega1 ((S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)) ∧
      A = Omega1 ⁅(S : Subgroup G), (S : Subgroup G)⁆

@[expose] def S_G88 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    Nat.card A = 4 → ¬ IsMulCommutative (S : Subgroup G) →
    ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∉ A →
    ∃ B : Subgroup G, B ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ∧ A ⊓ B = ⊥ ∧
      A ⊔ B = (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)

@[expose] def S_G89 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), GoldSetting G S A →
    Nat.card A = 4 → ¬ IsMulCommutative (S : Subgroup G) → False

end CFSG.Goldschmidt
