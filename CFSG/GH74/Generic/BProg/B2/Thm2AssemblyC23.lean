module

public import CFSG.GH74.Generic.BProg.B2.Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

namespace SD2

@[expose] def C23Kill : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H B : Subgroup G) (h : G),
    Stage2Setup G x K A M P Q → Stage2Concl1Core x K M Q H → Sym8A M B h →
      barIn M H ≠ barIn M K → False

end SD2

end CFSG.GH74.Generic.BProg.B2
