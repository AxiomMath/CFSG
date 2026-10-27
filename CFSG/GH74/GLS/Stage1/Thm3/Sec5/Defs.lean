module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Statements
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

section Notation

variable {G : Type} [Group G]

abbrev Cz (z : G) : Subgroup G := centralizer ({z} : Set G)

@[expose] def Oz (z : G) : Subgroup G := pPrimeCoreOf 2 (Cz z)

@[expose] def commBar (z : G) : Subgroup G := ⁅Cz z, Cz z⁆ ⊔ Oz z

@[expose] def Pof (S K : Subgroup G) : Subgroup G := S ⊓ K

@[expose] def Qof (S K : Subgroup G) : Subgroup G := S ⊓ cSec K

@[expose] def S1 (S K : Subgroup G) : Subgroup G := S ⊓ normalizer (K : Set G)

abbrev HatT (K : Subgroup G) : Type := ↥K ⧸ pPrimeCore 2 ↥K

@[expose] def Wof (S : Subgroup G) (a : G) : Subgroup G := S ⊓ centralizer ({a} : Set G)

@[expose] def Iof (K : Subgroup G) (a : G) : Subgroup G := pLayerOf 2 (K ⊓ centralizer ({a} : Set G))

@[expose] def Iall (z a : G) : Subgroup G :=
  pLayerOf 2 (Cz z ⊓ centralizer ({a} : Set G))

@[expose] def Jof (a : G) : Subgroup G := pLayerOf 2 (centralizer ({a} : Set G))

end Notation

structure Cfg5 (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) : Prop where
  std : Std4 G z S K₁ K₂
  hQ : Qz S z = zpowers z
  m₁ : pRank 2 ↥(Qof S K₁) = 1
  m₂ : pRank 2 ↥(Qof S K₂) = 1

structure Elt5 (G : Type) [Group G] (z : G) (S K₁ K₂ : Subgroup G) (a : G) : Prop where
  mem : a ∈ S
  inv : orderOf a = 2
  ne : a ∉ zpowers z
  f₁ : InducesFAut a K₁
  f₂ : InducesFAut a K₂

structure Ctr5 (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (a x : G) :
    Prop where
  cfg : Cfg5 G z S K₁ K₂
  elt : Elt5 G z S K₁ K₂ a
  comm : a ∈ commBar z
  extr : CFSG.ABGLocalTools.IsSylowOf 2 (Wof S a) (Cz z ⊓ centralizer ({a} : Set G))
  xP : x ∈ Pz S z
  x2 : orderOf x = 2
  xz : x ≠ z
  xnorm : ∀ s ∈ S, s * x * s⁻¹ = x ∨ s * x * s⁻¹ = x * z
  xa : a * x = x * a

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
