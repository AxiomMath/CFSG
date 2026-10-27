module

public import CFSG.GH74.Generic.BProg.Stage2Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

@[expose] def Stage2Thm3S1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G),
    Stage2Setup G x K A M P Q → Stage2Concl1 x K M Q H → Stage2Concl2 M →
      Stage2Cor2 x K A M H → A ≤ K → QShape1 (↥K ⧸ pPrimeCore 2 ↥K) →
        barIn M H = barIn M K → centralizer ({x} : Set G) ≤ M → pRank 2 ↥(CMbar M K) ≤ 1 →
          False

end CFSG.GH74.Generic.BProg.B2
