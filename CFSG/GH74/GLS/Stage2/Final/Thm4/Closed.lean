module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Prop17_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Ctx17 G z k S M →
    ¬ Thm4Concl z k S M → M = Cen z ∧ pPrimeCoreOf 2 M ≠ ⊥

@[expose] def Prop19_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Ctx17 G z k S M →
    M = Cen z → Thm4a M ∧ Thm4c z M

@[expose] def PSp4_oddCover : Prop :=
  ∀ (J K : Type) [Group J] [Group K] [Finite J] (f : J →* K), Function.Surjective f →
    Group.IsPerfect J → f.ker ≤ center J → Odd (Nat.card f.ker) → ∀ q : ℕ, Odd q →
      IVK.IsPSp4 K q → f.ker = ⊥

@[expose] def OddCoreOverC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ M ∈ maximalOverCentralizer z, Even (Nat.card ↥(generalizedFitting ↥M)) →
      pPrimeCoreOf 2 M ≠ ⊥ → M = Cen z

@[expose] def EvenOverC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    (∃ ε : Bool, k = Kind.l4 ε) → ∀ M ∈ maximalOverCentralizer z, Cen z < M →
      Even (Nat.card ↥(generalizedFitting ↥M))

end CFSG.GH74.GLS.Stage2.Final.Thm4
