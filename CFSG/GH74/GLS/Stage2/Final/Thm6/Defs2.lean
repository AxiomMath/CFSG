module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

@[expose] def TypePSp4 {G : Type} [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) (q : ℕ) : Prop :=
  k = Kind.psp4 ∧ ∃ L₁ L₂ : Subgroup (CentralizerBar z), Stage1PSp4 G z S q L₁ L₂

@[expose] def TypeCl {G : Type} [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) : Prop :=
  (∃ (ε : Bool) (q : ℕ), TypeL4 z k S ε q) ∨ ∃ q : ℕ, TypePSp4 z k S q

section Situations

variable {G : Type} [Group G] [Finite G]

@[expose] def F0 (z g : G) : Subgroup G := F20 z ⊓ Ag z g

@[expose] def H0 (z g : G) : Subgroup G := normalizer (F0 z g : Set G)

@[expose] def J0 (z g : G) : Subgroup G := pLayerOf 2 (H0 z g)

structure Case20A (z : G) (S : Subgroup G) (g : G) : Prop where
  t_mem : zc z g ∈ S
  t_ne : zc z g ∉ zpowers z
  inter : F20 z ⊓ Ag z g ≠ ⊥

structure SympCtx (z : G) (S : Subgroup G) (g : G) : Prop where
  y_mem : zc z g ∈ S
  swap : ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1Pair G z S q L₁ L₂ ∧ Swaps z (zc z g) L₁ L₂
  u_not : ¬ IsConj z (zc z g * z)

@[expose] def Iy (z g : G) : Subgroup G := Em (L20 z ⊓ centralizer ({zc z g} : Set G))

@[expose] def Hy (z g : G) : Subgroup G := centralizer (Iy z g : Set G)

@[expose] def Ey (z g : G) : Subgroup G := Fpi {r | r.Prime ∧ r ≠ 2} (Hy z g)

@[expose] def Jy (z g : G) : Subgroup G := Em (Hy z g)

end Situations

end CFSG.GH74.GLS.Stage2.Final.Thm6
