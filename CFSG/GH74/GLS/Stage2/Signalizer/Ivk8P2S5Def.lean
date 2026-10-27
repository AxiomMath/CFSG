module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

@[expose] def XfamR {G : Type} [Group G] (z : G) (M V : Subgroup G) : Set (Subgroup G) :=
  {X | X ≠ ⊥ ∧ X ≠ ⊤ ∧ (∀ v ∈ V, v ∈ normalizer (X : Set G)) ∧ ⁅X, zpowers z⁆ = X ∧
    Fpi (piF' M) X ⊓ M = ⊥ ∧ Fpi (piF M) X ≤ M}

@[expose] def XdR {G : Type} [Group G] (M : Subgroup G) (d : G) : Subgroup G :=
  Em (centralizer ({d} : Set G)) ⊔ Fpi (piF' M) (centralizer ({d} : Set G))

@[expose] def XDR {G : Type} [Group G] (M D : Subgroup G) : Subgroup G :=
  ⨆ d ∈ Dstar M D, XdR M d

@[expose] def Claim18Xd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (E : Subgroup G)
    (t : G), Ctx18 G z k S M p E t → ∀ d ∈ E, d ≠ 1 → ¬ centralizer ({d} : Set G) ≤ M →
      ¬ XdR M d ≤ M

@[expose] def Lemma18_8R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (E : Subgroup G)
    (t : G), Ctx18 G z k S M p E t →
      ¬ ∃ X ∈ XfamR z M (Vof M E), ∀ Y ∈ XfamR z M (Vof M E), Y ≤ X

@[expose] def Lemma18_9R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (E : Subgroup G)
    (t : G), Ctx18 G z k S M p E t → ∀ D : Subgroup G, D ≤ E → Nat.card ↥D = p ^ 2 →
      (Dstar M D).Nonempty → XDR M D = ⊤

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
