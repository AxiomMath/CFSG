module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Notation

variable {G : Type} [Group G]

@[expose] def A20 (z : G) : Subgroup G := OddCore z

@[expose] def F20 (z : G) : Subgroup G := Fm (OddCore z)

@[expose] def L20 (z : G) : Subgroup G := Em (Cen z)

@[expose] def Ag (z g : G) : Subgroup G := conjugate (OddCore z) g

@[expose] def zc (z g : G) : G := g⁻¹ * z * g

end Notation

@[expose] def Fused (ε : Bool) (q : ℕ) : Prop := q % 4 = (if ε then 1 else 3)

@[expose] def TypeL4 {G : Type} [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) (ε : Bool) (q : ℕ) : Prop :=
  k = Kind.l4 ε ∧ ∃ L₁ L₂ : Subgroup (CentralizerBar z), Stage1L4 G z S ε q L₁ L₂

section Concl

variable {G : Type} [Group G] [Finite G]

@[expose] def Conc201 (z : G) (k : Kind) (S M : Subgroup G) : Prop :=
  ∃ (ε : Bool) (q : ℕ), TypeL4 z k S ε q ∧ M = Cen z ∧
    ∃ K₁ K₂ : Subgroup G, IsCentralProd K₁ K₂ (Em M) ∧ HasSL2Model ↥K₁ (fun r => r = q) ∧
      HasSL2Model ↥K₂ (fun r => r = q) ∧
      IsCyclic ↥(pPrimeCoreOf 2 M) ∧
      ∃ t : G, IsConj z t ∧ t ∈ S ∧ t ∈ normalizer (K₁ : Set G) ∧
        Nat.card ↥(pPrimeCoreOf 2 M) ∣ Nat.card ↥(pPrimeCoreOf 2 (K₁ ⊓ centralizer ({t} : Set G))) ∧
        (t ∈ K₁ ⊔ K₂ ↔ Fused ε q)

structure Ctx20 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) : Prop where
  ctx17 : Ctx17 G z k S M
  thm4 : Thm4Concl z k S M

structure Fail20 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) : Prop where
  ctx : Ctx20 G z k S M
  notM12 : k ≠ Kind.m12
  odd_ne : pPrimeCoreOf 2 M ≠ ⊥
  fail : ¬ Conc201 z k S M

end Concl

end CFSG.GH74.GLS.Stage2.Final.Thm6
