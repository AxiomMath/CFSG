module

public import CFSG.GH74.GLS.Bg.Pu5.Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def L299F1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1 →
      ∀ K : Subgroup G, IsRigidRankOneComp z K →
        Nat.card ↥(S ⊓ cSec K) = 4 → ¬ IsCyclic ↥(S ⊓ cSec K) →
          ∃ s : G, s ∈ centralizer ({t} : Set G) ∧ s * s = z

@[expose] def L299F2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1 →
      ∀ K : Subgroup G, IsRigidRankOneComp z K →
        Nat.card ↥(S ⊓ cSec K) = 4 → ¬ IsCyclic ↥(S ⊓ cSec K) →
          ¬ ∃ s : G, s ∈ centralizer ({z} : Set G) ∧ s * s = t

end CFSG.GH74.GLS.Bg.Pu5
