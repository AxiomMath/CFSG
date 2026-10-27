module

public import CFSG.GH74.Generic.BProg.B3.S3Rk1Main2
public import CFSG.GH74.Generic.BProg.B3.S3Pump306a

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.ABGLocalTools Subgroup

theorem prop306aBarAt_of_inputs {G : Type} [Group G] [Finite G]
    (hC2 : C2CoverInput) {x : G} {K A : Subgroup G}
    (hLO : ∀ y : G, Setup30 G x K A y →
      pPrimeCoreOf 2 (Ly K y) ≤ pPrimeCoreOf 2 (centralizer ({y} : Set G))) :
    Prop306aBarAt x K A :=
  fun y h => prop306a_bar hC2 h (hLO y h)

end CFSG.GH74.Generic.BProg.B3
