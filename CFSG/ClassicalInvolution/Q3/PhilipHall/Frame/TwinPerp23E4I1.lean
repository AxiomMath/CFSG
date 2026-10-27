module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4I0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WEW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf18OddW

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open scoped commutatorElement


section E4I1

theorem p23E4WImg_proved (n : ℕ) : W.P23E4WImg n := by
  intro _ _ Y _ _ R S t K' Wg u e g hc _ _
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2
  have hW : Wg ∈ WSet (Om R) := hc.std.hW
  obtain ⟨η, ⟨S₀, hη, hinv⟩, hWη⟩ := id hW
  have hWS : Wg ≤ (S₀ : Subgroup Y) := by
    rw [hWη]
    exact iSup₂_le fun U hU => (hη.1 hU).2
  have hWn : ∀ s ∈ (S₀ : Subgroup Y), conjSub s Wg = Wg := by
    intro s hs
    rw [hWη, conjSub_iSup₂]
    apply le_antisymm
    · exact iSup₂_le fun U hU => le_iSup₂_of_le _ (hinv s hs U hU) le_rfl
    · refine iSup₂_le fun U hU => ?_
      have hU' : conjSub s⁻¹ U ∈ η := hinv s⁻¹ ((S₀ : Subgroup Y).inv_mem hs) U hU
      have : U = conjSub s (conjSub s⁻¹ U) := (conjSub_conjSub_inv s U).symm
      rw [this]
      exact le_iSup₂_of_le (conjSub s⁻¹ U) hU' le_rfl
  have hNe := normalizer_le_centralizer_e hc.data
  have heW : e ∈ Wg := by
    have he : e ∈ Wg ⊓ Asc77.centerIn (Subgroup.normalizer (Wg : Set Y)) := by
      rw [← hc.data.he]; exact Subgroup.subset_closure rfl
    exact (Subgroup.mem_inf.mp he).1
  have hS₀e : (S₀ : Subgroup Y) ≤ Subgroup.centralizer ({e} : Set Y) := fun s hs =>
    hNe (mem_normalizer_of_conjSub_eq (hWn s hs))
  obtain ⟨S₁, hS₁⟩ := E4I.exists_sylow_hull hΩ hc2 hS₀e
  have hWH := E4I.wHull_mem hΩ h2 hc2 hW hWS hWn heW hNe hS₁
  have hΛ : HypOmegaGen (TwinDisc.hullFam (Om R) e) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) (coreHull (Om R) e)
  have hΛ' : HypOmegaGen (TwinDisc.secFam (Om R) e) := TwinDisc.hypOmegaGen_secFam hΩ hc2
  have hmem := TwinThmEW.map_mem_WSet hΛ hΛ'
    (CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull (Om R) e)) hWH
  refine ⟨E4I.le_rLayer_of_mem_WSet hΩ h2 hc2 hW hWS hNe, fun V hV => ?_⟩
  have himg : W.wImage R Wg e ∈ WSet (TwinDisc.secFam (Om R) e) := hmem
  rw [hV] at himg
  exact himg

end E4I1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
