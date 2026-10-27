module

public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

structure Ctx17 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) (M : Subgroup G) :
    Prop where
  ctx : Stage2Ctx G z k S
  mem : M ∈ maximalOverCentralizer z
  even : Even (Nat.card ↥(generalizedFitting ↥M))

section Concl

variable {G : Type} [Group G]

@[expose] def H17A (M : Subgroup G) : Prop := Em M ⊔ Op 2 M ≠ ⊥

@[expose] def OddCover (z : G) (M : Subgroup G) : Prop :=
  ∀ h ∈ M, ∃ c ∈ Cen z, ∃ o ∈ pPrimeCoreOf 2 M, h = c * o

@[expose] def PSp4Layer (M : Subgroup G) (q : ℕ) : Prop := IVK.IsPSp4 ↥(Em M) q

@[expose] def Thm4a (M : Subgroup G) : Prop := pLayerOf 2 M = Em M

variable [Finite G]

@[expose] def Thm4b (z : G) (k : Kind) (S M : Subgroup G) : Prop :=
  Cen z < M → IsClassicalKind k ∧
    (∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), k = Kind.psp4 →
      Stage1PSp4 G z S q L₁ L₂ → PSp4Layer M q) ∧
    (∀ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), k = Kind.l4 ε →
      Stage1L4 G z S ε q L₁ L₂ → PSp4Layer M q)

@[expose] def Thm4c (z : G) (M : Subgroup G) : Prop :=
  M = Cen z → IsInternalDirectProduct (pPrimeCoreOf 2 M) (O2coreOf (O2Of M)) (O22Of (O2Of M))

@[expose] def Thm4Concl (z : G) (k : Kind) (S M : Subgroup G) : Prop :=
  Thm4a M ∧ Thm4b z k S M ∧ Thm4c z M

end Concl

@[expose] def Ch4Thm4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ M ∈ maximalOverCentralizer z, Even (Nat.card ↥(generalizedFitting ↥M)) → Thm4Concl z k S M

end CFSG.GH74.GLS.Stage2.Final.Thm4
