module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

@[expose] def O2RankOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ¬ Group.IsSolvable ↥(Cen z) → pRank 2 ↥(Op 2 (Cen z)) = 1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
