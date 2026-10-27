module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameCore
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51D4A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Frame

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem closure_zta_eq_closure_zt_az (a : G) :
    Subgroup.closure ({z, t, a} : Set G) = Subgroup.closure ({z, t, a * z} : Set G) := by
  have hz : z ∈ Subgroup.closure ({z, t, a * z} : Set G) := Subgroup.subset_closure (by simp)
  have hc : a * z ∈ Subgroup.closure ({z, t, a * z} : Set G) := Subgroup.subset_closure (by simp)
  have ha : a ∈ Subgroup.closure ({z, t, a * z} : Set G) := by
    have := (Subgroup.closure ({z, t, a * z} : Set G)).mul_mem hc
      ((Subgroup.closure ({z, t, a * z} : Set G)).inv_mem hz)
    simpa using this
  have hz' : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have ha' : a ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have hc' : a * z ∈ Subgroup.closure ({z, t, a} : Set G) :=
    (Subgroup.closure ({z, t, a} : Set G)).mul_mem ha' hz'
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
  · rintro x (rfl | rfl | rfl)
    · exact hz
    · exact Subgroup.subset_closure (by simp)
    · exact ha
  · rintro x (rfl | rfl | rfl)
    · exact hz'
    · exact Subgroup.subset_closure (by simp)
    · exact hc'

theorem tgt_coreAt_eq {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (c : Y) :
    TwinFrameTgt.coreAt R c = TwinADescent.coreAt c R := by
  unfold TwinFrameTgt.coreAt
  rw [TwinExitPf2.tightCore_subgroupOf_cent R c]
  exact Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c R)

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
