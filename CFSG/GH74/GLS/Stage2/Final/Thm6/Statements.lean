module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

@[expose] def Prop201 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Ctx20 G z k S M → k ≠ Kind.m12 →
    pPrimeCoreOf 2 M = ⊥ ∨ Conc201 z k S M

@[expose] def Thm6OddCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    (∀ ε : Bool, k ≠ Kind.l4 ε) → pPrimeCore 2 ↥(Cen z) = ⊥

@[expose] def Thm6OddCoreL4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool) (q : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)), Stage2Ctx G z (Kind.l4 ε) S → Stage1L4 G z S ε q L₁ L₂ →
      IsCyclic ↥(pPrimeCore 2 ↥(Cen z)) ∧ Nat.card ↥(pPrimeCore 2 ↥(Cen z)) ∣ (if ε then q - 1 else q + 1)

structure Thm6Leaves : Prop where

end CFSG.GH74.GLS.Stage2.Final.Thm6
