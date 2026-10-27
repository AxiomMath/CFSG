module

public import CFSG.GH74.GLS.Stage2.Local.P34S5Frat

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

variable {G : Type} [Group G] [Finite G] {z : G}

theorem ixz_le_jx_of_kgh (hK : KGH G) (hSch : P34.GHSchreier) {x : G}
    (hxnc : IsNonCentralInvolution x) (hzN : z ∈ centralizer ({x} : Set G))
    (hz2 : orderOf z = 2) : Ixz z x ≤ Jx x :=
  P34.Ixz_le_Jx_of_sections
    (P34.schreierSections_of_ghGroup hSch
      (Uniqueness.SU.SU0.GHGroup.of_kgh hK (P34.centralizer_ne_top_of_nonCentral hxnc))) hzN hz2

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1
