module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Notation

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

section Stmts

variable {G : Type} [Group G]

@[expose] def Hyp33 (x y : G) (K T V W : Subgroup G) (f z : G) : Prop :=
  Cfg3 x y K T V W f z ∧ pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f)

@[expose] def IsSpecial (x y : G) (K T : Subgroup G) (f : G) : Prop :=
  ∀ f' : G, FMax3 x y K f' → IsFMember x K T f' →
    Nat.card ↥(thompsonJ2 T ⊓ centralizer ({f'} : Set G)) ≤
      Nat.card ↥(thompsonJ2 T ⊓ centralizer ({f} : Set G))

end Stmts

end CFSG.GH74.GLS
