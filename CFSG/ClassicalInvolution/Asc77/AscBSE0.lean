module

public import CFSG.ClassicalInvolution.Asc77.AscBSDResid

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]


@[expose] def BootNoG2TwinThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
      D.tag i = .G2 → D.card = 3 → False

@[expose] def AEmptyG2Twin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
      D.tag i = .G2 → D.card = 3 → ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M

@[expose] def BootNoD4FiveComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootSetting p f K z → ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∀ i,
      (D.tag i = .POmegaPlus ∧ D.rank i = 4) → D.card = 5 → False

structure BootShapeResidualsNarrower : Prop where
  noAllA1 : BootNoAllA1 p f
  noG2TwinThree : BootNoG2TwinThree p f
  noG2D4Single : BootNoG2D4Single p f
  noD4FiveComp : BootNoD4FiveComp p f
  noSmallSingle : BootNoSmallSingle p f
  twinsCommute : BootTwinsCommute p f

end CFSG.ClassicalInvolution.Asc77.BSC
