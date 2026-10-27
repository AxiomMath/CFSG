module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3GXFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3GXSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22CNC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4MSp6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX

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

section Main


theorem v3LayerGenExConjAd_proved (n : ℕ) (hA : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) :
    V3LayerGenExConjAd n := by
  classical
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr W hW hu₁ hu₂ ha₃ ha₄ hno hc
  have h4 : Thm4RTwinBelow 3 n := TwinThmEW.t4Supply_of_twoClass n hA hP
  obtain ⟨z, τ, a, b, ε₀, hz, hτ, hF, hτz, hB', hτB', hBB', hnb, hnb'⟩ := v3_secFrameU hStd fr
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hCd := CoreData.of_S hStd.perp.core
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have h2 : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hCd.datum.twoGroup)
  have hmap := coreHull_map_eq_rLayer hΩ hc2 h2
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  have hsec := secGen_of_exit_conj hA hP h4 TwinDisc.e4O8TwinModel_of_certs
    TwinPerp23.E4M.e4Sp6FrameModel_of_certs hlt hS hF hB' hτB' hBB' hτz hnb hnb' hc hno
  have hτ2 : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
    calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [hd.hz.sq]; group
  exact layer_le_of_sec_gen hmap z τ hz hτ hd.hz.sq hτ2 hsec

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX
