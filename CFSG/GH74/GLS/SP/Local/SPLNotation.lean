module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.Basic
public import CFSG.GH74.GLS.LU.Local.SL2Aux

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local
open scoped Pointwise commutatorElement

structure SPLNot0 (G : Type) [Group G] where
  p : ℕ
  q : ℕ
  z : G
  S : Sylow 2 G
  K₁ : Subgroup G
  K₂ : Subgroup G
  t : G

namespace SPLNot0

variable {G : Type} [Group G] (D : SPLNot0 G)

@[expose] def K : Subgroup G := D.K₁ ⊔ D.K₂

@[expose] def S₁ : Subgroup G := (D.S : Subgroup G) ⊓ D.K

@[expose] def C : Subgroup G := centralizer ({D.z} : Set G)

@[expose] def F : Subgroup G := pPrimeCoreOf 2 (centralizer (D.S₁ : Set G))

@[expose] def Ct : Subgroup G := centralizer ({D.t} : Set G)

@[expose] def F₀ : Subgroup G := D.F ⊓ D.Ct

@[expose] def d : ℕ := if D.q % 4 = 1 then D.q - 1 else D.q + 1

@[expose] def n : ℕ := (D.d).factorization 2 + 1

@[expose] def e : ℕ := D.d / 2 ^ (D.d).factorization 2

end SPLNot0

structure SPLNot1 (G : Type) [Group G] extends SPLNot0 G where
  h₁ : G
  w₁ : G

namespace SPLNot1

variable {G : Type} [Group G] (D : SPLNot1 G)

@[expose] def H₁ : Subgroup G := zpowers D.h₁

@[expose] def h₂ : G := D.t * D.h₁ * D.t⁻¹

@[expose] def H₂ : Subgroup G := zpowers D.h₂

@[expose] def H : Subgroup G := D.H₁ ⊔ D.H₂

@[expose] def H₀ : Subgroup G := zpowers (D.h₁ * D.h₂)

@[expose] def w₂ : G := D.t * D.w₁ * D.t⁻¹

@[expose] def w : G := D.w₁ * D.w₂

end SPLNot1

structure SPLNot2 (G : Type) [Group G] extends SPLNot1 G where
  A : Subgroup G
  I : Subgroup G
  x : G

structure SPLNot3 (G : Type) [Group G] extends SPLNot2 G where
  X₁ : Subgroup G
  X₁' : Subgroup G
  Y₁ : Subgroup G
  a : G

namespace SPLNot3

variable {G : Type} [Group G] (D : SPLNot3 G)

@[expose] def X₂ : Subgroup G := conjBy D.t D.X₁

@[expose] def X₂' : Subgroup G := conjBy D.t D.X₁'

@[expose] def X₃ : Subgroup G := conjBy D.a D.Y₁

@[expose] def X₄ : Subgroup G := conjBy D.w₁ D.X₃

@[expose] def X : Subgroup G := D.X₁ ⊔ D.X₂

@[expose] def R₂ : Subgroup G := D.X₂ ⊔ D.X₃ ⊔ D.X₄

@[expose] def R₁ : Subgroup G := D.X₁ ⊔ D.X₂ ⊔ D.X₃

@[expose] def P : Subgroup G := D.X₁ ⊔ D.R₂

@[expose] def B : Subgroup G := D.H ⊔ D.P

@[expose] def M₁ : Subgroup G := D.B ⊔ zpowers D.t

@[expose] def M₂ : Subgroup G := normalizer (D.X₂ : Set G)

@[expose] def root (i : ℤ) : Subgroup G :=
  if i = 1 then D.X₄ else if i = 2 then D.X₂ else if i = 3 then D.X₃ else if i = 4 then D.X₁ else
  if i = -1 then conjBy D.t D.X₄ else if i = -2 then D.X₂' else
  if i = -3 then conjBy (D.w₁ * D.t * D.w₁) D.X₃ else if i = -4 then D.X₁' else ⊥

@[expose] def Nw : Subgroup G := Subgroup.closure ((D.H : Set G) ∪ {D.t, D.w₁})

end SPLNot3

structure SPLNot4 (G : Type) [Group G] extends SPLNot3 G where
  J : Subgroup G

namespace SPLNot4

variable {G : Type} [Group G] (D : SPLNot4 G)

@[expose] def J₁ : Subgroup G := conjBy (D.a * D.w₁) D.J

end SPLNot4

end CFSG.GH74.GLS.SP.Local
