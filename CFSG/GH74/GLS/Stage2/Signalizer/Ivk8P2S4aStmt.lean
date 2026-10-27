module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Def

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

@[expose] def Lemma18_5R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ)
    (E : Subgroup G) (t : G), Ctx18 G z k S M p E t →
    ∀ X ∈ XfamR z M (Vof M E), X = Em X ⊔ Fpi (piF' M) X

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
