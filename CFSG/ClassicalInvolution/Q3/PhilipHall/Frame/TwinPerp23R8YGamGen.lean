module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamSec
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf25Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Cert


variable {n : ℕ}

theorem p23E8LayerGen_proved : P23E8LayerGen n := by
  intro _ _ Y _ _ R S t K' W u e g hc _ hA5 _
  classical
  obtain ⟨x, vH, v', hvx, hxx, hvH, hzv, hvH2, hgen⟩ := section_gen hc hA5
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hmap := TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2 h2
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) u) with hN
  have hNodd : Odd (Nat.card N) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull (Om R) u)
  have hL : ∀ h : ↥(coreHull (Om R) u), hcoeHom (Om R) u h ∈ rLayer (Om R) u := fun h => by
    rw [← hmap]
    exact ⟨(h : ↥(Subgroup.centralizer ({u} : Set Y))), h.2, rfl⟩
  have hmem := mem_sup_of_quot_gen N hNodd hxx hvH2 hgen
  have hP₁ : (Subgroup.centralizer ({x} : Set ↥(coreHull (Om R) u))).map (hcoeHom (Om R) u) ≤
      rLayer (Om R) u ⊓ Subgroup.centralizer ({u * e} : Set Y) := by
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨hL h, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hh
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← hvx, ← map_mul, ← map_mul, this]
  have hP₂ : (Subgroup.centralizer ({vH} : Set ↥(coreHull (Om R) u))).map (hcoeHom (Om R) u) ≤
      rLayer (Om R) u ⊓ Subgroup.centralizer ({t} : Set Y) := by
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨hL h, ?_⟩
    have h1 : hcoeHom (Om R) u h * v' = v' * hcoeHom (Om R) u h := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hh
      rw [← hvH, ← map_mul, ← map_mul, this]
    have h2' : hcoeHom (Om R) u h * u = u * hcoeHom (Om R) u h :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcoeHom_mem_centralizer (Om R) u h)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rcases hzv with ht | ht
    · rw [ht]; exact h1
    · rw [ht]
      calc hcoeHom (Om R) u h * (u * v') = (hcoeHom (Om R) u h * u) * v' := by group
        _ = (u * hcoeHom (Om R) u h) * v' := by rw [h2']
        _ = u * (hcoeHom (Om R) u h * v') := by group
        _ = u * (v' * hcoeHom (Om R) u h) := by rw [h1]
        _ = (u * v') * hcoeHom (Om R) u h := by group
  have hP₃ : N.map (hcoeHom (Om R) u) ≤
      rLayer (Om R) u ⊓ oddCoreOf (Subgroup.centralizer ({u} : Set Y)) := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨hL m, TwinDisc.oddCore_coreHull_le hΩ hc2 hm⟩
  intro l hl
  have hl' : l ∈ (coreHull (Om R) u).map (Subgroup.centralizer ({u} : Set Y)).subtype := by
    rw [hmap]; exact hl
  obtain ⟨c, hcH, rfl⟩ := hl'
  have hmem' := Subgroup.mem_map_of_mem (hcoeHom (Om R) u) (hmem ⟨c, hcH⟩)
  rw [Subgroup.map_sup, Subgroup.map_sup] at hmem'
  exact sup_le_sup (sup_le_sup hP₁ hP₂) hP₃ hmem'

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
