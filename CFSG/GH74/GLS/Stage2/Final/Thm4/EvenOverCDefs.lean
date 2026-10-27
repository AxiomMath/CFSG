module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

structure Rigid {G : Type} [Group G] [Finite G] (z : G) (M : Subgroup G) : Prop where
  z_ord : orderOf z = 2
  coatom : IsCoatom M
  cen_le : Cen z ≤ M
  odd : Odd (Nat.card ↥(generalizedFitting ↥M))
  oddCore : pPrimeCoreOf 2 (Cen z) = ⊥

structure PairData (Y : Type) [Group Y] [Finite Y] : Prop where
  oddCore : pPrimeCore 2 Y = ⊥
  fs_eq : generalizedFitting Y = layer Y
  exists_pair : ∃ L₁ L₂ : Subgroup Y, L₁ ≠ L₂ ∧ {K : Subgroup Y | IsComponent K} = {L₁, L₂} ∧
    (∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) ∧ ∃ s : Y, conjugate L₁ s = L₂ ∧ conjugate L₂ s = L₁

end CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver
