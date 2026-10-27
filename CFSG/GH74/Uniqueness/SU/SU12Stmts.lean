module

public import CFSG.GH74.Uniqueness.SU.SU10Stmts

public section

namespace CFSG.GH74.Uniqueness.SU.SU12

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8
  CFSG.GH74.Uniqueness.SU.SU10 CFSG.Blueprint

variable {G : Type} [Group G]

section Finite

variable [Finite G]

structure Hyp22 (S : Sylow 2 G) (M : Subgroup G) (z : G) : Prop extends Hyp21 S M z where
  not_le : ¬ centralizer ({z} : Set G) ≤ M
  oPrime_le : (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map
    (centralizer ({z} : Set G)).subtype ≤ M
  shape : K.IsTwoAlt (Hbar (centralizer ({z} : Set G))) 9 ∧
    K.IsTwoAlt ↥(hbarImage (centralizer ({z} : Set G)) M) 8

@[expose] def Prop221Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (M : Subgroup G) (z : G), Hyp22 S M z →
    pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥

end Finite

end CFSG.GH74.Uniqueness.SU.SU12
