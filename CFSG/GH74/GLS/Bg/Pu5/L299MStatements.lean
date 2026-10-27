module

public import CFSG.GH74.GLS.Bg.Pu5.Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def L299FourS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S : Subgroup G), Cfg G z t S →
    Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1 →
      ∀ K : Subgroup G, IsRigidRankOneComp z K →
        Nat.card ↥(S ⊓ cSec K) = 4 → ¬ IsCyclic ↥(S ⊓ cSec K) → False

end CFSG.GH74.GLS.Bg.Pu5
