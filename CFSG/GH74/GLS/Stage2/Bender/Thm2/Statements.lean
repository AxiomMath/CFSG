module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Thm2False : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    (∀ M ∈ maximalOverCentralizer z, Odd (Nat.card ↥(generalizedFitting ↥M))) →
    (∀ M ∈ maximalOverCentralizer z, ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥(generalizedFitting ↥M)) → False

structure Thm2Leaves : Prop where

end CFSG.GH74.GLS.Stage2.Bender.Thm2
