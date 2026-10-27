module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip

structure Cfg (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G) : Prop where
  simple : IsKProperSimple G
  gen4 : Gen4 G
  rank : 3 ≤ pRank 2 G
  hz : orderOf z = 2
  hzK : z ∈ rigidProduct z
  conj : IsConj z t
  tC : t ∈ centralizer ({z} : Set G)
  tZ : t ∉ zStar (rigidProduct z)
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))
  tS : t ∈ S
  ext : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({t} : Set G))
    (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))

@[expose] def L292LP : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
    ∀ (a b : G) (K : Subgroup G), IsRigidRankOneComp a K → orderOf b = 2 →
      b ∈ centralizer ({a} : Set G) → b ∈ cSec K →
        ∀ y ∈ zStar K, (∃ n : ℕ, y ^ (2 ^ n) = 1) → y ∈ centralizer ({b} : Set G) →
          y ∈ zStar (rigidProduct b)

@[expose] def L292TP : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
    ∀ (a b : G) (K : Subgroup G), IsRigidRankOneComp a K → orderOf b = 2 →
      b ∈ centralizer ({a} : Set G) → b ∈ cSec K →
        ∀ y : G, orderOf y = 2 → y ∈ centralizer ({a} : Set G) → y ∈ centralizer ({b} : Set G) →
          y ∈ zStar (rigidProduct b) → y ∈ cSec K

@[expose] def L293 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    ∀ u : G, orderOf u = 2 → u ∈ centralizer ({z} : Set G) → u ∈ centralizer ({t} : Set G) →
      ∀ K : Subgroup G, IsRigidRankOneComp z K → u ∈ cSec K →
        ∀ L : Subgroup G, IsRigidRankOneComp t L → u ∈ cSec L → False

@[expose] def L294a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    (∀ K : Subgroup G, IsRigidRankOneComp z K → ¬ InducesFAut t K) ∧
    (∀ L : Subgroup G, IsRigidRankOneComp t L → ¬ InducesFAut z L)

@[expose] def L294b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    (∃ K : Subgroup G, IsRigidRankOneComp z K ∧ t ∉ normalizer (K : Set G)) →
      Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 2 ∧ S ⊓ zStar (rigidProduct z) = zpowers z

@[expose] def IsFour {G : Type} [Group G] (U : Subgroup G) : Prop :=
  CFSG.IsElementaryAbelian 2 ↥U ∧ Nat.card ↥U = 4

@[expose] def L295 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    ∀ K : Subgroup G, IsRigidRankOneComp z K → ∀ U : Subgroup G, IsFour U →
      U ≤ centralizer ({z, t} : Set G) ⊓ cSec K → z ∈ U →
      (∀ y ∈ S ⊓ K, orderOf y = 2 → y ∈ U) →
        (∀ L : Subgroup G, IsRigidRankOneComp t L → U ≤ normalizer (L : Set G)) ∧
        (∀ L : Subgroup G, IsRigidRankOneComp t L → ∀ u ∈ U, orderOf u = 2 → ¬ InducesFAut u L) ∧
        (∀ L : Subgroup G, IsRigidRankOneComp t L → ∀ u ∈ U, u ∉ zpowers z → ¬ InducesInner u L)

@[expose] def L296 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    S ⊓ zStar (rigidProduct z) = zpowers z ∧
    ∀ K : Subgroup G, IsRigidRankOneComp z K →
      pRank 2 ↥(centralizer ({z, t} : Set G) ⊓ cSec K) = 1

@[expose] def L297 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    ∃ S' : Sylow 2 G, ∀ g : G,
      (g ∈ (S' : Subgroup G) ∧ (∀ s ∈ (S' : Subgroup G), s * g = g * s) ∧ g ^ 2 = 1) ↔ g ∈ zpowers z

@[expose] def L299 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1 →
      ∀ P : Sylow 2 ↥(rigidSectionCentralizer z),
        IsCyclic ↥P.toSubgroup ∨ IsNonabelianMaximalClassTwoGroup ↥P.toSubgroup

end CFSG.GH74.GLS.Bg.Pu5
