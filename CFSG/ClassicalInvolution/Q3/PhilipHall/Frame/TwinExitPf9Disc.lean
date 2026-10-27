module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Hyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelSp62
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelD42
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelM12
public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscAlpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscClaims

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

namespace TwinDisc

@[expose] def TwinDiscBaseV₃ (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TwinExitPf9.TwinFrameULiftPairSec (CoreAssembly.conjClass (tightCore R))

section Generic

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem hyp51_allV₃ (hB : TwinDiscBaseV₃ n) (h4 : Thm4RTwinBelow 3 n)
    (h : TwinCoreHyp n Y R S t)
    (hnc : ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))) :
    ∀ B ∈ TwinFrame.frameSet (CoreAssembly.conjClass (tightCore R)), Hyp51 B := by
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
  obtain ⟨S₀, h₀⟩ := TwinEdge.twinCoreHyp_core h
  have hid := TwinEdge.tightCore_idem R
  have key : ∀ B ∈ TwinFrame.frameSet (CoreAssembly.conjClass (tightCore (tightCore R))),
      Hyp51 B := by
    intro B hB'
    refine TwinExitPf9.hyp51_of_mem_frameSet_new5 TwinCentRes.modelFactSp62
      TwinCentRes.modelFactD42_of_cert TwinCentRes.modelFactM12_of_certs h4 h₀ hid hZ
      TL4.d4OddAutInnerNC3_proved ?_ ?_ ?_ hB'
    · rw [hid]
      rintro _ ⟨g, rfl⟩
      have hR := Q8Datum.isSolvable h.datum
      have hK : Group.IsSolvable ↥(tightCore R) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (tightCore_le R))
          (Subgroup.inclusion_injective _)
      exact isSolvable_conjSub_of hK g
    · rw [hid]; exact hB Y R S t h hnc
    · rw [hid]; exact TwinUActsPf.twinFrameUActs_of_core h
  rwa [hid] at key

theorem alphaStepsBaseV₃ (hB : TwinDiscBaseV₃ n) (h4 : Thm4RTwinBelow 3 n)
    (s : Setting n R S t₀ K K' z u J t W) :
    AlphaSteps (CoreAssembly.conjClass (tightCore R)) :=
  ⟨s.core.hyp, TwinFrame.trans_conjClass _, hyp51_allV₃ hB h4 s.core s.disc⟩

end Generic

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
