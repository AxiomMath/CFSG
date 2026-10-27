module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def Lem510_cyc' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    pRank 2 ↥(Qof S K) = 1 → ∀ b ∈ S, b * b ∈ Qof S K → InducesFAut b K → b ∉ cSec K →
      IsCyclic ↥(Qof S K ⊔ zpowers b) →
        (∃ F : Subgroup G, Std4r1 G z S K F ∧ IsCyclic ↥F) ∨
          ∃ a ∈ S, orderOf a = 2 ∧ InducesFAut a K ∧ a ∉ cSec K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
