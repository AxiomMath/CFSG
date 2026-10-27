module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fCtx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem v3AE6E3_of {n : ℕ} (hC : V3AE6EComm n) (hDN : V3AE6DNorm n) (hI : V3AE6I n) :
    V3AE6E3 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  have hE : V3AE6E n := A6b.v3AE6E_proved
  have hD : V3AE6D n := v3AE6D_of hE hC
  obtain ⟨C⟩ := nonempty_ctx hD hDN hI H fr
  have hinv := conjInvariant_conjClass (tightCore R)
  obtain ⟨hab, hP₁⟩ := A6Hx.ae6E3_elemAb_le hE hC H fr hx
  obtain ⟨j, -, hjx, hjt⟩ := exists_cent_conj C hx
  obtain ⟨hh, -, -⟩ := hx
  obtain ⟨hτt, hττ⟩ := A6Hx.tau_edge H fr
  obtain ⟨hxt, hxx⟩ := A6Hx.x_edge H fr hh
  have hxP : h * (y * t * y⁻¹) * h⁻¹ ∈ ae6P Ω[R] t := by
    refine hP₁ (Subgroup.subset_closure ?_)
    simp
  have hxPτ : h * (y * t * y⁻¹) * h⁻¹ ∈ ae6P Ω[R] (y * t * y⁻¹) := by
    have h1 := conj_mem_conjSub (n := j) hxP
    rwa [A6Hx.ae6P_conj hinv, hjt, hjx] at h1
  have hτPx : y * t * y⁻¹ ∈ ae6P Ω[R] (h * (y * t * y⁻¹) * h⁻¹) := by
    have h1 := conj_mem_conjSub (n := j) hxt
    rwa [A6Hx.ae6P_conj hinv, hjx, hjt] at h1
  refine ⟨hab, hP₁, ?_, ?_⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ (rfl | rfl | rfl)
    exacts [hτt, hττ, hxPτ]
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ (rfl | rfl | rfl)
    exacts [hxt, hτPx, hxx]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
