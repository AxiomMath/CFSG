module

public import CFSG.Assembly.OddCoreSpan
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)

@[expose] def S_N17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A K : Subgroup G), A ≤ S →
    IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) →
    goldschmidtOddCore G = ⊥ → IsComponentOf K ⊤ →
    goldschmidtSimpleType (K ⧸ Subgroup.center K) → InducesOmega1 A K S →
    ∀ a ∈ A, ∃ x ∈ A ⊓ K, ∀ y ∈ K, a⁻¹ * y * a = x⁻¹ * y * x

@[expose] def S_N19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), A ≤ S →
    IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) →
    Subgroup.normalClosure (A : Set G) = ⊤ →
    ∀ K : Subgroup G, IsComponentOf K ⊤ → K.Normal ∧ ⁅K, A⁆ ≠ ⊥

@[expose] def S_N20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    goldschmidtLayer G = ⊥ → A = ⊤ ∧ CoreConclusion G S A

@[expose] def S_N21 : Prop :=
  ∀ n : ℕ, IH n → ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G),
    CoreHyp G S A → ∀ K : Subgroup G, IsComponentOf K ⊤ →
    ((Subgroup.centralizer (K : Set G)).subgroupOf (K ⊔ A)).index < n →
    goldschmidtSimpleType (K ⧸ Subgroup.center K) ∧ InducesOmega1 A K S

@[expose] def S_N22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    IH (Nat.card G) → goldschmidtLayer G ≠ ⊥ →
    (IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a) ∨
    (∃ K : Subgroup G, IsComponentOf K ⊤ ∧ K.Normal ∧ IsSimpleGroup K ∧ K ⊔ A = ⊤ ∧
      Subgroup.centralizer (K : Set G) = ⊥ ∧ ¬ A ≤ K) ∨
    ((∀ K : Subgroup G, IsComponentOf K ⊤ →
        ((Subgroup.centralizer (K : Set G)).subgroupOf (K ⊔ A)).index < Nat.card G) ∧
      CFSG.Open.pCore 2 G ⊔ goldschmidtLayer G = ⊤ ∧
      Subgroup.centralizer (goldschmidtLayer G : Set G) = CFSG.Open.pCore 2 G)

@[expose] def S_N23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    IH (Nat.card G) → ¬ IsComponentOf (⊤ : Subgroup G) ⊤ →
    (∀ K : Subgroup G, IsComponentOf K ⊤ →
      goldschmidtSimpleType (K ⧸ Subgroup.center K) ∧ InducesOmega1 A K S) →
    CFSG.Open.pCore 2 G ⊔ goldschmidtLayer G = ⊤ →
    Subgroup.centralizer (goldschmidtLayer G : Set G) = CFSG.Open.pCore 2 G →
    A = CFSG.Open.pCore 2 G ⊔ Omega1 ((S : Subgroup G) ⊓ goldschmidtLayer G)

@[expose] def S_simpleConcl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (S : Sylow 2 G) (A : Subgroup G),
    CoreConclusion G S A ↔ goldschmidtSimpleType G ∧ A = Omega1 (S : Subgroup G)

@[expose] def S_B3setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    IH (Nat.card G) → ∀ K : Subgroup G, K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → K ⊔ A = ⊤ → Subgroup.centralizer (K : Set G) = ⊥ → ¬ A ≤ K →
    A ⊓ K ≠ ⊥ ∧ goldschmidtSimpleType K ∧ A ⊓ K = Omega1 ((S : Subgroup G) ⊓ K)

@[expose] def S_N24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    ∀ K : Subgroup G, K.Normal → IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → K ⊔ A = ⊤ →
    Subgroup.centralizer (K : Set G) = ⊥ → ¬ A ≤ K → goldschmidtSimpleType K →
    A ⊓ K = Omega1 ((S : Subgroup G) ⊓ K) →
    IsMulCommutative ((S : Subgroup G) ⊓ K : Subgroup G) → False

@[expose] def S_N25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    ∀ K : Subgroup G, K.Normal → IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → K ⊔ A = ⊤ →
    Subgroup.centralizer (K : Set G) = ⊥ → ¬ A ≤ K → goldschmidtSimpleType K →
    A ⊓ K = Omega1 ((S : Subgroup G) ⊓ K) →
    ¬ IsMulCommutative ((S : Subgroup G) ⊓ K : Subgroup G) → False

@[expose] def S_B2setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    IH (Nat.card G) → CFSG.Open.IsQuasisimple G → Subgroup.center G ≠ ⊥ →
    IsPGroup 2 (Subgroup.center G) ∧ goldschmidtSimpleType (G ⧸ Subgroup.center G) ∧
    A.map (QuotientGroup.mk' (Subgroup.center G)) =
      Omega1 ((S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G)))

@[expose] def S_N26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    CFSG.Open.IsQuasisimple G → Subgroup.center G ≠ ⊥ →
    goldschmidtSimpleType (G ⧸ Subgroup.center G) →
    A.map (QuotientGroup.mk' (Subgroup.center G)) =
      Omega1 ((S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G))) →
    IsMulCommutative ((S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G))) → False

@[expose] def S_N27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    CFSG.Open.IsQuasisimple G → goldschmidtSimpleType (G ⧸ Subgroup.center G) →
    A.map (QuotientGroup.mk' (Subgroup.center G)) =
      Omega1 ((S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G))) →
    ¬ IsMulCommutative ((S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G))) →
    Subgroup.center G ≤ A

@[expose] def S_N28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), CoreHyp G S A →
    CFSG.Open.IsQuasisimple G → goldschmidtSimpleType (G ⧸ Subgroup.center G) →
    A.map (QuotientGroup.mk' (Subgroup.center G)) =
      Omega1 ((S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G))) →
    Subgroup.center G ≤ A → CoreConclusion G S A

@[expose] def S_N29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ S : Sylow 2 G, IsMulCommutative (S : Subgroup G) → ∀ A : Subgroup G, A ≤ S → A ≠ ⊥ →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) →
    goldschmidtSimpleType G ∧ A = S ∧ A = Omega1 (S : Subgroup G)

@[expose] def S_N30 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], fusionIsBenderGroup G → ∀ S : Sylow 2 G,
    ¬ IsMulCommutative (S : Subgroup G) → ∀ A : Subgroup G, A ≤ S → A ≠ ⊥ → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) →
    goldschmidtSimpleType G ∧ A = Omega1 (S : Subgroup G) ∧ A = sylowCenter (S : Subgroup G)

@[expose] def S_N31_exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), A ≤ S → A ≠ ⊥ →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) →
    ∃ U : Subgroup G, U ≤ A ∧ IsMinStronglyClosed (S : Subgroup G) U

@[expose] def S_N31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (S : Sylow 2 G) (A U : Subgroup G), A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U →
    IsElemAbelian 2 U ∧ 4 ≤ Nat.card U ∧
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (U : Set G) ∧
    (∀ x g : G, x ∈ Subgroup.normalizer (U : Set G) →
      g⁻¹ * x * g ∈ Subgroup.normalizer (U : Set G) → (∃ k : ℕ, x ^ (2 ^ k) = 1) →
      ∃ m ∈ Subgroup.normalizer (U : Set G), m⁻¹ * x * m = g⁻¹ * x * g) ∧
    (∀ H : Subgroup G, H ≤ Subgroup.normalizer (U : Set G) →
      (H.subgroupOf (Subgroup.normalizer (U : Set G))).index ≠ 2) ∧
    ∀ V : Subgroup G, V ≤ U → Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) →
      V = ⊥ ∨ V = U

@[expose] def S_N36 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → ∀ (S : Sylow 2 G) (U : Subgroup G), U ≤ S → IsElemAbelian 2 U →
    fusionStronglyClosed (U : Set G) (S : Subgroup G) →
    (∀ w ∈ U, w ≠ 1 → let M := normalClosureIn (Subgroup.centralizer ({w} : Set G)) U
      goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊥) →
    (∀ u ∈ U, u ≠ 1 → ∀ w ∈ U, w ≠ 1 →
      oddCoreOf (Subgroup.centralizer ({u} : Set G)) ⊓ Subgroup.centralizer ({w} : Set G) ≤
        oddCoreOf (Subgroup.centralizer ({w} : Set G))) ∧
    ∀ w ∈ U, w ≠ 1 → Subgroup.centralizer ({w} : Set G) =
      oddCoreOf (Subgroup.centralizer ({w} : Set G)) ⊔
        (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.normalizer (U : Set G))

@[expose] def S_N37 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → ∀ (S : Sylow 2 G) (A U : Subgroup G), A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → 8 ≤ Nat.card U →
    (∀ w ∈ U, w ≠ 1 → let M := normalClosureIn (Subgroup.centralizer ({w} : Set G)) U
      goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊥) →
    let W := CFSG.Assembly.Dichotomy.oddCoreSpan U
    let Y := Subgroup.normalizer (W : Set G)
    Odd (Nat.card W) ∧
    (∀ u ∈ U, u ≠ 1 →
      W ⊓ Subgroup.centralizer ({u} : Set G) = oddCoreOf (Subgroup.centralizer ({u} : Set G))) ∧
    Subgroup.normalizer (U : Set G) ≤ Y ∧
    (∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ Y) ∧
    (∀ P : Subgroup G, P ≤ S → 4 ≤ Nat.card (P ⊓ U : Subgroup G) →
      Subgroup.normalizer (P : Set G) ≤ Y) ∧
    oddCoreOf Y = W ∧
    fusionIsTI ((U.subgroupOf Y).map (QuotientGroup.mk' (W.subgroupOf Y))) ∧
    (∀ u ∈ U, u ≠ 1 → ∀ g : G, g⁻¹ * u * g ∈ Y → g ∈ Y) ∧
    (fusionIsTI U ↔ ⁅W, U⁆ = ⊥)

@[expose] def S_N39 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → 3 ≤ CFSG.Assembly.twoRank G → ¬ CFSG.Assembly.IsComponentType G →
    (∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) →
    ∀ (S : Sylow 2 G) (U : Subgroup G), U ≤ S → U ≠ ⊥ → IsElemAbelian 2 U →
    fusionStronglyClosed (U : Set G) (S : Subgroup G) → False

@[expose] def S_N40 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.twoRank G = 2 → ∀ (S : Sylow 2 G) (A : Subgroup G), A ≤ S → A ≠ ⊥ →
    IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) →
    IsMulCommutative (S : Subgroup G) ∨ Nonempty (G ≃* PSU3 2 2)

@[expose] def S_propH_compType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IH (Nat.card G) → CFSG.Assembly.IsComponentType G → 3 ≤ CFSG.Assembly.twoRank G →
    (∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) →
    ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G) →
    ∀ A U : Subgroup G, A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set G) (S : Subgroup G) → U ≤ A →
    IsMinStronglyClosed (S : Subgroup G) U → False

end CFSG.Goldschmidt
