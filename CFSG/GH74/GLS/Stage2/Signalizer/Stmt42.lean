module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def SDWr_rank2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), SDorWr S → pRank 2 ↥S ≤ 2

end CFSG.GH74.GLS.Stage2.Signalizer
