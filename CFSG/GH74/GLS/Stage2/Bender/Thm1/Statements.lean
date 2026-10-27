module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Thm1PrimePower : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    (∀ M ∈ maximalOverCentralizer z, Odd (Nat.card ↥(generalizedFitting ↥M))) →
    ∀ M ∈ maximalOverCentralizer z, IsPrimePowerGrp ↥(generalizedFitting ↥M)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
