module

public import CFSG.GH74.GLS.Stage2.Final.ClassicalClosed

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Main
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec7

@[expose] def ECInter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    (k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε) →
      (CFSG.layer ↥(Cen z)).map (Cen z).subtype ⊓ OddCore z = ⊥

structure ClassicalData : Prop where
  center : ModelCenter
  oddCore : ModelOddCore
  oneClass : ModelOneClass
  disjoint : ModelsDisjoint
  layerBar : ModelLayerBar
  ecInter : ECInter

end CFSG.GH74.GLS.Stage2.Final
