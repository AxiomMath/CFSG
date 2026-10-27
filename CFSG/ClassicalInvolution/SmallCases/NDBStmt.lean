module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.SmallConnP1
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinCtx
public import CFSG.ClassicalInvolution.Asc77.WP3FrameStmt
public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51
public import CFSG.ClassicalInvolution.Asc77.WP3LayerPair
public import CFSG.ClassicalInvolution.Balance.LayerGenerationField
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupFrame
public import CFSG.ClassicalInvolution.Balance.Theorem5Fuzzy
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

structure Setting (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  member : IsClassicalMember p f K z
  below : CITBelowU p f (Nat.card G)
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  dconn : Disconnected.DConnected (𝒞 K)
  noBoot : ¬ BootData p f (𝒞 K)

structure SettingCore (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  member : IsClassicalMember p f K z
  below : CITBelowU p f (Nat.card G)
  dconn : Disconnected.DConnected (𝒞 K)

variable {p f} in
theorem Setting.toCore {K : Subgroup G} {z : G} (h : Setting p f K z) : SettingCore p f K z :=
  ⟨h.nonabelian, h.odd, h.five, h.member, h.below, h.dconn⟩

@[expose] def PSpShape (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∃ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily Ω z) z, D.card = 2 ∧
    ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧ D.tag i₁ = .PSp ∧
      D.rank i₁ = 2 ∧ ∃ x, x ≠ 1 ∧ x ∈ (D.hom i₀).range ∧ x ∈ (D.hom i₁).range

@[expose] def NoDataShapeCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      Disconnected.DConnected (𝒞 K) → ¬ BootData p f (𝒞 K) →
        (∃ A : Subgroup G, Balance.Theorem5.FuzzyFrameOn p f (𝒞 K) A) ∨
          Asc77.ChainShape p f (𝒞 K) z ∨ Asc77.TwinExactShape p f K z ∨ PSpShape p f (𝒞 K) z

@[expose] def FuzzyFrameExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → ∀ A : Subgroup G, ¬ Balance.Theorem5.FuzzyFrameOn p f (𝒞 K) A

@[expose] def PSpEverywhere (Ω : Set (Subgroup G)) : Prop :=
  ∀ L ∈ Ω, ∀ w : G, IsClassicalMember p f L w → PSpShape p f Ω w

@[expose] def PSpCaseP1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → PSpEverywhere p f (𝒞 K) → LocalOddCentral (𝒞 K) {z}

structure PSpAxis (Ω : Set (Subgroup G)) (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G) :
    Prop where
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  mem₃ : K₃ ∈ Ω
  cls₁ : IsClassicalMember p f K₁ z₁
  cls₂ : IsClassicalMember p f K₂ z₂
  cls₃ : IsClassicalMember p f K₃ z₃
  prod : z₁ * z₂ = z₃
  tq₁₂ : z₂ ∈ trivialOnQuot K₁
  tq₁₃ : z₃ ∈ trivialOnQuot K₁
  tq₂₁ : z₁ ∈ trivialOnQuot K₂
  tq₂₃ : z₃ ∈ trivialOnQuot K₂
  tq₃₁ : z₁ ∈ trivialOnQuot K₃
  tq₃₂ : z₂ ∈ trivialOnQuot K₃
  ht₁ : t₁ ∈ K₁
  ht₂ : t₂ ∈ K₂
  ht₃ : t₃ ∈ K₃
  sq₁ : t₁ * t₁ = z₁
  sq₂ : t₂ * t₂ = z₂
  sq₃ : t₃ * t₃ = z₃
  ct₁₂ : t₁ * t₂ = t₂ * t₁
  ct₁₃ : t₁ * t₃ = t₃ * t₁
  ct₂₃ : t₂ * t₃ = t₃ * t₂
  hw₁ : w₁ ∈ K₁
  hw₂ : w₂ ∈ K₂
  inv₁ : w₁ * t₁ = t₁ * z₁ * w₁
  inv₂ : w₂ * t₂ = t₂ * z₂ * w₂
  cw₁₂ : w₁ * t₂ = t₂ * w₁
  cw₁₃ : w₁ * t₃ = t₃ * w₁
  cw₂₁ : w₂ * t₁ = t₁ * w₂
  cw₂₃ : w₂ * t₃ = t₃ * w₂
  elem : CFSG.Open.IsElemAbelian 2 (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃)
  card : Nat.card (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) = 8

@[expose] def AxisExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → PSpEverywhere p f (𝒞 K) →
      ∃ (K₂ K₃ : Subgroup G) (z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂

@[expose] def AxisHyp51Classical : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → PSpEverywhere p f (𝒞 K) →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
          ∀ c ∈ Subgroup.closure ({z₁, z₂} : Set G), c ≠ 1 →
            Asc77.Hyp51At (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) c

@[expose] def AxisFrameSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → PSpEverywhere p f (𝒞 K) →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
          Asc77.FrameSideTwoStar p f (𝒞 K) (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) {K₁, K₂, K₃}

@[expose] def AxisHyp51S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → PSpEverywhere p f (𝒞 K) →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
          ∀ c ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃, c ∉ Subgroup.closure ({z₁, z₂} : Set G) →
            Asc77.Hyp51At (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) c

@[expose] def AxisP1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → PSpEverywhere p f (𝒞 K) →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
          RankThreeBalance (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) →
            rankTwoSpan (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) = ⊤ → LocalOddCentral (𝒞 K) {z₁}

@[expose] def PSpCaseP1Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    SettingCore p f K z → PSpEverywhere p f (𝒞 K) → LocalOddCentral (𝒞 K) {z}

@[expose] def AxisExistsCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    SettingCore p f K z → PSpEverywhere p f (𝒞 K) →
      ∃ (K₂ K₃ : Subgroup G) (z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂

@[expose] def AxisHyp51ClassicalCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    SettingCore p f K z → PSpEverywhere p f (𝒞 K) →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
          ∀ c ∈ Subgroup.closure ({z₁, z₂} : Set G), c ≠ 1 →
            Asc77.Hyp51At (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) c

@[expose] def AxisFrameSideCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    SettingCore p f K z → PSpEverywhere p f (𝒞 K) →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
          Asc77.FrameSideTwoStar p f (𝒞 K) (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) {K₁, K₂, K₃}

@[expose] def AxisHyp51SCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    SettingCore p f K z → PSpEverywhere p f (𝒞 K) →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
          ∀ c ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃, c ∉ Subgroup.closure ({z₁, z₂} : Set G) →
            Asc77.Hyp51At (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) c

@[expose] def AxisP1Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    SettingCore p f K z → PSpEverywhere p f (𝒞 K) →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
          RankThreeBalance (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) →
            rankTwoSpan (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) = ⊤ → LocalOddCentral (𝒞 K) {z₁}

theorem PSpCaseP1.of_core (h : PSpCaseP1Core p f) : PSpCaseP1 p f :=
  fun G _ _ _ K z hS => h G K z hS.toCore

theorem AxisExists.of_core (h : AxisExistsCore p f) : AxisExists p f :=
  fun G _ _ _ K z hS => h G K z hS.toCore

theorem AxisHyp51Classical.of_core (h : AxisHyp51ClassicalCore p f) : AxisHyp51Classical p f :=
  fun G _ _ _ K z hS => h G K z hS.toCore

theorem AxisFrameSide.of_core (h : AxisFrameSideCore p f) : AxisFrameSide p f :=
  fun G _ _ _ K z hS => h G K z hS.toCore

theorem AxisHyp51S.of_core (h : AxisHyp51SCore p f) : AxisHyp51S p f :=
  fun G _ _ _ K z hS => h G K z hS.toCore

theorem AxisP1.of_core (h : AxisP1Core p f) : AxisP1 p f :=
  fun G _ _ _ K z hS => h G K z hS.toCore

end CFSG.ClassicalInvolution.NDB
