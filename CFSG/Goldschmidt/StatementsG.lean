module

public import CFSG.Goldschmidt.BasicG
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped MatrixGroups

@[expose] def S_G28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A N A₀ : Subgroup G), IsElemAbelian 2 A → 4 ≤ Nat.card A →
    N ≤ Subgroup.normalizer (A : Set G) →
    (∀ V : Subgroup G, V ≤ A → N ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = A) →
    A₀ ≤ A → (A₀.subgroupOf A).index = 2 → ∀ a ∈ A, a ≠ 1 → ∃ n ∈ N, n⁻¹ * a * n ∈ A₀

@[expose] def S_G210 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A X : Subgroup G) (y : G), ONanHyp A X y →
    (∀ x ∈ X, conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) ≠
        A ⊓ Subgroup.centralizer ({y} : Set G) → ∀ k : ℕ,
      conjSub (y ^ k) (conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G))) =
        conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) →
      y ^ k ∈ Subgroup.centralizer (A : Set G)) →
    Nat.card (A ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) = 2 ∧
      ∀ b ∈ A, ∀ c ∈ A, b ≠ 1 → c ≠ 1 → ∃ x ∈ X, x⁻¹ * b * x = c

@[expose] def S_G211 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A X : Subgroup G) (y : G), ONanHyp A X y →
    (∀ X₀ : Subgroup G, X₀ ≤ X → X ⊓ Subgroup.centralizer (A : Set G) ≤ X₀ →
      (X₀.subgroupOf X).index ≠ 2) →
    (∀ x ∈ X, conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) =
        A ⊓ Subgroup.centralizer ({y} : Set G) →
      x⁻¹ * y * x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A : Set G)) →
    Nat.card A = 8 ∧ Nat.card (A ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) = 2 ∧
      ((X ⊓ Subgroup.centralizer (A : Set G)).subgroupOf X).index = 21 ∧
      ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∉ Subgroup.centralizer (A : Set G)

@[expose] def S_G31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H A : Subgroup G), IsSStarIn H A →
    (∀ L : Subgroup (H ⧸ goldschmidtOddCore H),
      IsComponentOf L (barOf H (normalClosureIn H A)) →
      IsSStarIn (preOf H L) (A ⊓ preOf H L) ∧
      preOf H L = normalClosureIn (preOf H L) (A ⊓ preOf H L) ⊔ oddCoreOf (preOf H L) ∧
      A = A ⊓ preOf H L ⊔
        A ⊓ preOf H (Subgroup.centralizer (L : Set (H ⧸ goldschmidtOddCore H)))) ∧
    normalClosureIn H A ⊓
        Subgroup.centralizer
          (oddCoreOf (CFSG.fittingSubgroupOf (normalClosureIn H A)) : Set G) ≤
      GorensteinWalter.generalizedFittingSubgroupOf H

@[expose] def S_G32 : Prop :=
  ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L], IsGoldTypeI L → ∀ T : Sylow 2 L,
    ∃ D : Subgroup L, D ≤ Subgroup.normalizer ((T : Subgroup L) : Set L) ∧ IsCyclic D ∧
      Odd (Nat.card D) ∧ (T : Subgroup L) ⊓ D = ⊥ ∧
      (T : Subgroup L) ⊔ D = Subgroup.normalizer ((T : Subgroup L) : Set L) ∧
      D ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L) = ⊥ ∧ ⁅(T : Subgroup L), D⁆ = T ∧
      Omega1 (T : Subgroup L) =
        (T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L) ∧
      (∀ x ∈ Omega1 (T : Subgroup L), ∀ x' ∈ Omega1 (T : Subgroup L), x ≠ 1 → x' ≠ 1 →
        ∃ d ∈ D, d⁻¹ * x * d = x') ∧
      (¬ IsMulCommutative (T : Subgroup L) →
        ⁅(T : Subgroup L), (T : Subgroup L)⁆ =
          (T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L) ∧
        (∀ x ∈ (T : Subgroup L),
          x ^ 2 ∈ (T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L)) ∧
        ∀ X : Subgroup L,
          (T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L) ≤ X →
          X ≤ T → D ≤ Subgroup.normalizer (X : Set L) →
          X = (T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L) ∨ X = T) ∧
      (∀ n : ℕ, 3 ≤ n → Nonempty (L ≃* PSL(2, GaloisField 2 n)) →
        Nat.card (T : Subgroup L) = 2 ^ n ∧ Nat.card D = 2 ^ n - 1) ∧
      (∀ n : ℕ, 1 ≤ n → Nonempty (L ≃* Sz n) →
        Nat.card ((T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L) :
          Subgroup L) = 2 ^ (2 * n + 1) ∧
        Nat.card (T : Subgroup L) = 2 ^ (2 * (2 * n + 1)) ∧
        Nat.card D = 2 ^ (2 * n + 1) - 1) ∧
      (∀ n : ℕ, 2 ≤ n → Nonempty (L ≃* PSU3 2 n) →
        Nat.card ((T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L) :
          Subgroup L) = 2 ^ n ∧
        Nat.card (T : Subgroup L) = 2 ^ (3 * n) ∧
        Nat.card D = (2 ^ (2 * n) - 1) / Nat.gcd 3 (2 ^ n + 1)) ∧
      (∀ g : L, (T : Subgroup L) ⊓ conjSub g T ≠ ⊥ → conjSub g T = T) ∧
      (∀ P Q : Sylow 2 L, P ≠ T → Q ≠ T → ∃ t ∈ (T : Subgroup L), t • P = Q) ∧
      (∃ T' : Sylow 2 L, T' ≠ T ∧ D ≤ Subgroup.normalizer ((T' : Subgroup L) : Set L) ∧
        Subgroup.normalizer ((T : Subgroup L) : Set L) ⊓
          Subgroup.normalizer ((T' : Subgroup L) : Set L) = D ∧
        ∀ P : Sylow 2 L, D ≤ Subgroup.normalizer ((P : Subgroup L) : Set L) → P = T ∨ P = T') ∧
      IsCoatom (Subgroup.normalizer ((T : Subgroup L) : Set L)) ∧
      ∀ M : Subgroup L, (T : Subgroup L) ≤ M → M ≠ ⊤ →
        M ≤ Subgroup.normalizer ((T : Subgroup L) : Set L)

@[expose] def S_G33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A T : Subgroup G), L.Normal → CFSG.Open.IsQuasisimple L →
    IsGoldTypeI L → IsSStarIn L A → normalClosureIn L A = L → fusionIsSylowIn 2 T L → A ≤ T →
    ∀ α : G, α ∈ Subgroup.centralizer (A : Set G) → α ∈ Subgroup.normalizer (T : Set G) →
      (∀ t ∈ T, α⁻¹ * t * α * t⁻¹ ∈ A) → α ∈ T ⊔ Subgroup.centralizer (L : Set G)

@[expose] def S_G34 : Prop :=
  ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L], IsGoldTypeII L → ∀ A : Subgroup L,
    IsSStarIn ⊤ A → A ≠ ⊥ →
    fusionIsSylowIn 2 A ⊤ ∧
    (IsGoldL2 L →
      Nonempty (Subgroup.normalizer (A : Set L) ≃* alternatingGroup (Fin 4)) ∧
      ∀ (p f : ℕ) [Fact p.Prime], 0 < f → Nonempty (L ≃* PSL(2, GaloisField p f)) →
        ∀ a ∈ A, a ≠ 1 →
        (p ^ f % 4 = 1 →
          Nonempty (Subgroup.centralizer ({a} : Set L) ≃* DihedralGroup ((p ^ f - 1) / 2))) ∧
        (p ^ f % 4 = 3 →
          Nonempty (Subgroup.centralizer ({a} : Set L) ≃* DihedralGroup ((p ^ f + 1) / 2)))) ∧
    (IsGoldJR L →
      oddCoreOf (Subgroup.centralizer (A : Set L)) =
        (Subgroup.center (Subgroup.normalizer (A : Set L))).map
          (Subgroup.normalizer (A : Set L)).subtype ∧
      IsCyclic (oddCoreOf (Subgroup.centralizer (A : Set L))) ∧
      ((Subgroup.centralizer (A : Set L)).subgroupOf (Subgroup.normalizer (A : Set L))).index =
        21 ∧
      ∃ x ∈ Subgroup.normalizer (A : Set L), ∃ x' ∈ Subgroup.normalizer (A : Set L),
        x * x' * x⁻¹ * x'⁻¹ ∉ Subgroup.centralizer (A : Set L)) ∧
    ∀ a ∈ A, a ≠ 1 → IsCoatom (Subgroup.centralizer ({a} : Set L)) ∨
      (Nonempty (L ≃* alternatingGroup (Fin 5)) ∧ IsCoatom (Subgroup.normalizer (A : Set L)) ∧
        ∀ M : Subgroup L, IsCoatom M → Subgroup.centralizer ({a} : Set L) ≤ M →
          M = Subgroup.normalizer (A : Set L))

@[expose] def S_G35 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A Y : Subgroup G), L.Normal → CFSG.Open.IsQuasisimple L →
    IsGoldTypeII L → IsSStarIn L A → A ≠ ⊥ →
    (⁅Y, A⁆ = ⊥ →
      Odd (((L ⊔ Subgroup.centralizer (L : Set G)).subgroupOf Y).index) ∧
      ∃ y ∈ Y, Y ≤ Subgroup.zpowers y ⊔ (L ⊔ Subgroup.centralizer (L : Set G))) ∧
    ∀ a ∈ A, a ≠ 1 → L ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Y : Set G) →
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsPGroup q Y) →
      Y ≤ L ⊔ Subgroup.centralizer (L : Set G) ∧
        ∃ y ∈ Y, Y ≤ Subgroup.zpowers y ⊔ Subgroup.centralizer (L : Set G)

@[expose] def S_GNewPair : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → IsPGroup 2 (Subgroup.center L) →
    Subgroup.center L ≠ ⊥ →
    ((∃ n : ℕ, 2 ≤ n ∧ Nonempty (L ⧸ Subgroup.center L ≃* Sz n)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ Nonempty (L ⧸ Subgroup.center L ≃* PSU3 2 f))) →
    ∀ T : Sylow 2 L,
    (∀ b ∈ (T : Subgroup L), ∀ c ∈ (T : Subgroup L),
      (∀ x ∈ (T : Subgroup L), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center L) →
      (∀ x ∈ (T : Subgroup L), c * x * c⁻¹ * x⁻¹ ∈ Subgroup.center L) → b * c = c * b) →
    ∀ b ∈ (T : Subgroup L), (∀ x ∈ (T : Subgroup L), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center L) →
      ∀ x ∈ (T : Subgroup L), x * b = b * x

@[expose] def S_G36 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H A : Subgroup G), IsSStarIn H A → IsElemAbelian 2 A →
    ∀ L : Subgroup G, GorensteinWalter.IsComponentOf L (normalClosureIn H A) →
    ∃ y ∈ L ⊓ Subgroup.normalizer (A : Set G), Odd (orderOf y) ∧
      (∀ b ∈ ⁅A, Subgroup.zpowers y⁆, ∀ c ∈ ⁅A, Subgroup.zpowers y⁆, b ≠ 1 → c ≠ 1 →
        ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c) ∧
      A ⊓ Subgroup.centralizer ({y} : Set G) = A ⊓ Subgroup.centralizer (L : Set G) ∧
      ((∀ x ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (L : Set G),
          x⁻¹ * y * x ∈ Subgroup.zpowers y ⊔ L ⊓ Subgroup.centralizer (A : Set G)) ∨
        (IsGoldSz8Cover L ∧
          ((L ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
            (L ⊓ Subgroup.normalizer (A : Set G))).index = 56 ∧
          y ∉ Subgroup.centralizer (A : Set G) ∧ y ^ 7 ∈ Subgroup.centralizer (A : Set G) ∧
          ∀ x ∈ L ⊓ Subgroup.normalizer (A : Set G),
            x⁻¹ * y * x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A : Set G) →
            x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A : Set G)))

@[expose] def S_G37 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H A : Subgroup G), IsSStarIn H A → IsElemAbelian 2 A →
    ∀ a ∈ A, a ≠ 1 →
    ∀ X : Subgroup G, X ≤ H →
    H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) →
    X = GorensteinWalter.componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X) →
    (⁅X, Subgroup.zpowers a⁆ ≤ GorensteinWalter.generalizedFittingSubgroupOf H ∧
      (⁅X, Subgroup.zpowers a⁆.subgroupOf
        (GorensteinWalter.generalizedFittingSubgroupOf H)).IsSubnormal) ∧
    (∀ K : Subgroup G, GorensteinWalter.IsComponentOf K X →
      K ≤ Subgroup.centralizer (oddCoreOf H : Set G) →
      ∃ L : Subgroup G, GorensteinWalter.IsComponentOf L H ∧ K ≤ L ∧
        (K = L ∨ (IsGoldL2 K ∧ K ≤ Subgroup.centralizer ({a} : Set G) ∧ IsGoldJR L ∧
          L ≤ normalClosureIn H A))) ∧
    oddCoreOf (CFSG.fittingSubgroupOf X) ≤ normalClosureIn H A ⊔ oddCoreOf H ∧
    ∀ L : Subgroup G, GorensteinWalter.IsComponentOf L H →
      ¬ oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.centralizer (L : Set G) →
      L ≤ normalClosureIn H A ∧ IsGoldL2 L ∧
        oddCoreOf (CFSG.fittingSubgroupOf X) ≤ L ⊔ H ⊓ Subgroup.centralizer (L : Set G) ∧
        (∃ y ∈ oddCoreOf (CFSG.fittingSubgroupOf X),
          oddCoreOf (CFSG.fittingSubgroupOf X) ≤
            Subgroup.zpowers y ⊔ Subgroup.centralizer (L : Set G)) ∧
        ⁅A ⊓ L, oddCoreOf (CFSG.fittingSubgroupOf X)⁆ ≠ ⊥

@[expose] def S_G38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H A : Subgroup G), IsSStarIn H A → IsElemAbelian 2 A →
    ∀ A₀ : Subgroup G,
    A₀ ≤ A → ¬ IsCyclic A₀ → ∀ p : ℕ, p.Prime → p ≠ 2 →
    (⨅ a : {a : G // a ∈ A₀ ∧ a ≠ 1},
        GorensteinWalter.qCoreOf (H ⊓ Subgroup.centralizer ({a.1} : Set G)) p) ≤
      GorensteinWalter.qCoreOf H p

@[expose] def S_G311 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H A : Subgroup G), IsSStarIn H A → ∀ p : ℕ, p.Prime →
    p ≠ 2 → ∀ P : Subgroup G, Maximal (· ∈ sigN H A p) P →
    IsPGroup p (GorensteinWalter.generalizedFittingSubgroupOf H) →
    H ≤ Subgroup.normalizer (CFSG.Glauberman.ZJ P : Set G)

@[expose] def S_G312 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H A : Subgroup G), IsSStarIn H A → ∀ p : ℕ, p.Prime →
    p ≠ 2 → CFSG.Open.pRank p (GorensteinWalter.qCoreOf H p) ≤ 2 →
    (∃ n : ℕ, (derivedSeries (normalClosureIn H A ⊔ oddCoreOf H : Subgroup G) n).map
        (normalClosureIn H A ⊔ oddCoreOf H).subtype ≤
      Subgroup.centralizer (GorensteinWalter.qCoreOf H p : Set G)) ∧
    fusionIsSylowIn p (GorensteinWalter.qCoreOf H p)
      ((normalClosureIn H A ⊔ oddCoreOf H) ⊓ Subgroup.centralizer
        (GorensteinWalter.pResidualOf (GorensteinWalter.generalizedFittingSubgroupOf H) p :
          Set G))

@[expose] def S_G4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → 3 ≤ CFSG.Assembly.twoRank G →
    (∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) →
    ∀ (S : Sylow 2 G) (A U : Subgroup G), A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → GoldSetting G S U

@[expose] def S_G7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → CFSG.Assembly.IsComponentType G → 3 ≤ CFSG.Assembly.twoRank G →
    (∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) →
    ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G) →
    ∀ A U : Subgroup G, A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → 8 ≤ Nat.card U → False

@[expose] def S_G8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → CFSG.Assembly.IsComponentType G → 3 ≤ CFSG.Assembly.twoRank G →
    (∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) →
    ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G) →
    ∀ A U : Subgroup G, A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → Nat.card U = 4 → False

end CFSG.Goldschmidt
