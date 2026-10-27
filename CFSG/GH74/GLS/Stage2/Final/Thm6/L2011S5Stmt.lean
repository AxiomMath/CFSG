module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs2

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def L2011S5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S → TypeCl z k S →
    ∀ t ∈ S1 S z, orderOf t = 2 →
      ∀ c ∈ Cen z, ∃ a ∈ OddCore z, ∃ l ∈ LC z, ∃ σ ∈ S, ∃ d ∈ Cen z ⊓ centralizer ({t} : Set G),
        c = a * l * σ * d

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
