module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf68Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.ClassicalInvolution.Q3.TL3T1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

section

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

theorem twin_mem_DSet {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} (hP : Q3CL.PartIHypG Ω)
    (h2g : ∀ J ∈ Ω, IsPGroup 2 ↥J) {W : Subgroup Y} (hW : W ∈ WSet Ω) {t : Y} (htW : t ∈ W)
    {J : Subgroup Y} (hJ : J ∈ Ω) (ht : IsUniqueInvolution J t) : J ∈ DSet Ω W := by
  have c0 : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hWC : W ≤ Subgroup.centralizer ({t} : Set Y) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (c0.comm_W w hw t htW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  obtain ⟨ρ, hρK, hρR⟩ := exists_rep_in_T c0 hP.cls hT hWT hJ ht
  have h1 : ρ.R ∈ DSet Ω W := ρ.hR
  have h2 : IsSylow2In ρ.R ρ.K := ρ.hRK
  rw [hρK] at h2
  rw [hρR] at h1 h2
  have hJT : J = T ⊓ J := h2.2.2 J le_rfl (h2g J hJ) inf_le_right
  rw [← hJT] at h1
  exact h1

end

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
