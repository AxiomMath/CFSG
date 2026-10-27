module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3HexA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf6Solv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Comp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace Std20Frame

variable {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem commutator_component_modOdd3 (d : Std20Frame K K' J S R R' W V z t)
    {M : Subgroup G} (hM : M ∈ CoreAssembly.conjClass K) (hzM : IsUniqueInvolution M z)
    {L : Subgroup (CFSG.ClassicalInvolution.Balance.OddQuot z)} (hL : CFSG.IsComponent L) : ⁅L, modOdd z M⁆ = ⊥ := by
  have hsubC : IsSubnormal M (Subgroup.centralizer ({z} : Set G)) :=
    Q3CL.ClassicalClause.isSubnormal_of_uniqueInvolution d.late_cls hM hzM
  have hMC : M ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hsubC
  have hsolv : Group.IsSolvable ↥(modOdd z M) :=
    isSolvable_modOdd3 hMC (d.isSolvable_member hM)
  rcases CFSG.LocalCores.component_subnormal_subgroup hL (isSubnormal_modOdd3 hsubC) with h | h
  · exfalso
    have : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect ↥L := hL.1.1
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance
  · exact h

end Std20Frame

end Comp


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
