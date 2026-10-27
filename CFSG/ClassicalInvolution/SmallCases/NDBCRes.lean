module

public import CFSG.ClassicalInvolution.SmallCases.NDBStmt
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

@[expose] def HasTwin (K : Subgroup G) (z : G) : Prop :=
  ∃ T ∈ 𝒞 K, T ≠ K ∧ IsClassicalMember p f T z

@[expose] def HasTwoTwins (K : Subgroup G) (z : G) : Prop :=
  ∃ T₁ ∈ 𝒞 K, ∃ T₂ ∈ 𝒞 K, T₁ ≠ K ∧ T₂ ≠ K ∧ T₁ ≠ T₂ ∧ IsClassicalMember p f T₁ z ∧
    IsClassicalMember p f T₂ z

@[expose] def TwinShapeWeak (K : Subgroup G) (z : G) : Prop :=
  Asc77.TwinLieShape p f (𝒞 K) z ∧ HasTwin p f K z

@[expose] def NoDataShapeCoverWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      Disconnected.DConnected (𝒞 K) → ¬ BootData p f (𝒞 K) →
        (∃ A : Subgroup G, Balance.Theorem5.FuzzyFrameOn p f (𝒞 K) A) ∨
          Asc77.ChainShape p f (𝒞 K) z ∨ TwinShapeWeak p f K z ∨ PSpShape p f (𝒞 K) z

@[expose] def NoAllA1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z →
      ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z,
        ¬ ∀ i, D.tag i = .PSL ∧ D.rank i = 2

@[expose] def NoExoticSingle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → ¬ HasTwin p f K z →
      ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z, ∀ i,
        ¬ (D.tag i = .G2 ∨ D.tag i = .trialityD4 ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
          (D.tag i = .POmegaMinus ∧ D.rank i = 4))

@[expose] def NoG2D4Twin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → HasTwin p f K z →
      ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z, ∀ i,
        ¬ (D.tag i = .G2 ∨ D.tag i = .trialityD4)

@[expose] def NoD4Twins : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → HasTwoTwins p f K z →
      ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z, ∀ i,
        ¬ (D.tag i = .POmegaPlus ∧ D.rank i = 4)

end CFSG.ClassicalInvolution.NDB
