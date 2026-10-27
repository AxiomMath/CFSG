module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootMain
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
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]


structure BootSetting {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  member : IsClassicalMember p f K z
  below : CITBelowU p f (Nat.card G)
  dconn : DConnected (𝒞 K)
  data : BootData p f (𝒞 K)
  noTriple : ¬ IndepTriple p f (𝒞 K)

@[expose] def BootNoAllA1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z,
      ¬ ∀ i, D.tag i = .PSL ∧ D.rank i = 2

@[expose] def BootNoG2D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
      ¬ (D.tag i = .G2 ∨ D.tag i = .trialityD4)

@[expose] def BootNoM3Twin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
      (D.tag i = .PSL ∨ D.tag i = .PSU) → D.rank i = 3 → D.card ≤ 2

@[expose] def BootNoSmallSingle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z,
      D.card = 2 → ∀ i,
        ¬ ((D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
          (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4))

@[expose] def BootNoManyTwins : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
      Asc77.ListedTwin (D.tag i) (D.rank i) → D.card ≤ 3

@[expose] def BootTwinsCommute : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ T ∈ 𝒞 K, T ≠ K → IsClassicalMember p f T z → Commutes K T

structure BootShapeResidualsW : Prop where
  noAllA1 : BootNoAllA1 p f
  noG2D4 : BootNoG2D4 p f
  noM3Twin : BootNoM3Twin p f
  noSmallSingle : BootNoSmallSingle p f
  noManyTwins : BootNoManyTwins p f

structure BootShapeResiduals : Prop extends BootShapeResidualsW p f where
  twinsCommute : BootTwinsCommute p f

end CFSG.ClassicalInvolution.Asc77.BSC
