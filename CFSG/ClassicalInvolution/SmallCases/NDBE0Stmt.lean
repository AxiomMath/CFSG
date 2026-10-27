module

public import CFSG.ClassicalInvolution.SmallCases.NDBC1
public import CFSG.ClassicalInvolution.Asc77.WP3FrameStarE
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

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

section Statements

variable (p f : ℕ) [Fact p.Prime]

structure ExoticBase {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  member : IsClassicalMember p f K z
  below : CITBelowU p f (Nat.card G)
  dconn : Disconnected.DConnected (𝒞 K)

@[expose] def ExoticShape {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∃ D : LocalLieSystemAt p f (exactFamily Ω z) z, D.card = 2 ∧ ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧
    D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧ (D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4)

@[expose] def ExoticHyp51ZT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K J K' : Subgroup G) (z t z' : G),
    ExoticBase p f K z → ¬ HasTwin p f K z →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) → ExoticShape p f (𝒞 K) z →
        Asc77.ChainFrameData (𝒞 K) K J K' z t z' →
          Asc77.Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) (z * t)

@[expose] def ExoticFrameG2D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    ExoticBase p f K z → ¬ HasTwin p f K z →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) → p ^ f ≠ 9 →
        ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
          (D.tag i = .G2 ∨ D.tag i = .trialityD4) →
            ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
              Asc77.FuzzyFrameDataStarE p f (𝒞 K) L₀ z₀ A S a ∧ Asc77.Hyp51 A

@[expose] def ExoticFrameG2D4Nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    ExoticBase p f K z → ¬ HasTwin p f K z →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) → p ^ f = 9 →
        ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
          (D.tag i = .G2 ∨ D.tag i = .trialityD4) →
            ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
              Asc77.FuzzyFrameDataStarE p f (𝒞 K) L₀ z₀ A S a ∧ Asc77.Hyp51 A

variable {p f}

end Statements

section Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

structure ExoticCtx (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (K : Subgroup G) (z : G) where
  hS : ExoticBase p f K z
  hnoT : ¬ HasTwin p f K z
  hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A
  D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z
  card_eq : D.card = 2
  i₀ : Fin D.card
  i₁ : Fin D.card
  ne : i₀ ≠ i₁
  tag₀ : D.tag i₀ = .PSL
  rank₀ : D.rank i₀ = 2
  tag₁ : D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4
  K₀ : modOdd z (exactCore z K) =
    ((Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D).psi i₀).range

namespace ExoticCtx

noncomputable abbrev X {K : Subgroup G} {z : G} (C : ExoticCtx p f K z) :
    Asc77.XCtx p f (𝒞 K) z :=
  Cover.toXCtx C.hS.nonabelian C.hS.odd C.hS.five C.hS.member C.hS.below C.D

noncomputable abbrev psi {K : Subgroup G} {z : G} (C : ExoticCtx p f K z) (j : Fin C.D.card) :
    (compModel C.D j).K →* OddQuot z :=
  C.X.psi j

end ExoticCtx

end Ctx

end CFSG.ClassicalInvolution.NDB
