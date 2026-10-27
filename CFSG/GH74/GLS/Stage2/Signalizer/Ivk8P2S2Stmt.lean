module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Final.Thm4

@[expose] def Lemma17_7B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail17 G z k S M →
    pLayerOf 2 M ≠ ⊥ →
    (∀ J : Subgroup G, IsPCompIn 2 M J → pPrimeCoreOf 2 J ≤ centralizer (J : Set G)) →
      ∀ u : G, orderOf u = 2 → u ∈ centralizer (pPrimeCoreOf 2 M : Set G) → u = z

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
