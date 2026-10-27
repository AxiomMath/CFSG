module

public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.GH74.Generic.JStar2Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

structure Setup30 (G : Type) [Group G] [Finite G] (x : G) (K A : Subgroup G) (y : G) : Prop where
  hyp : Hyp2 G
  circ : IsJ2Circ x K
  shape : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)
  src : IsSource2 x K A
  rank1 : pRank 2 ↥(CxK x K) ≤ 1
  y_mem : y ∈ A ⊓ K
  y_ord : orderOf y = 2

noncomputable abbrev Ly (K : Subgroup G) (y : G) : Subgroup G :=
  pLayerOf 2 (K ⊓ centralizer ({y} : Set G))

@[expose] def IsZT (x y : G) (T : Subgroup G) : Prop :=
  IsSylowOf 2 T (centralizer ({x} : Set G)) ∧ x ∈ T ∧ y ∈ T ∧ (∀ t ∈ T, t * y = y * t) ∧
    ∀ z ∈ T, (∀ t ∈ T, t * z = z * t) → z * z = 1 → z = 1 ∨ z = x ∨ z = y ∨ z = x * y

end CFSG.GH74.Generic.BProg.B3
