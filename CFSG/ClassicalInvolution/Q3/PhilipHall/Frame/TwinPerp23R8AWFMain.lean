module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AWTr
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4I0

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section AWFib

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem w_le_rLayer (hc : P23Cfg n Y R S t K' W u e g) : W ≤ rLayer (Om R) e := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hd := hc.data
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  obtain ⟨S', hWS'⟩ := hW2.exists_le_sylow
  exact E4I.le_rLayer_of_mem_WSet hΩ h2 hc2 hd.hW hWS' (normalizer_le_centralizer_e hd)

theorem exists_weaklyClosed_of_cfg (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ S₀ : Sylow 2 Y, Sec7.WeaklyClosedIn W (S₀ : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := CoreData.of_S hc.std.perp.core
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have htr : ∀ K₁ ∈ Om R, ∀ J ∈ Om R, ∃ a : Y, conjSub a K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  obtain ⟨S₀, -, hwc, -⟩ := exists_weaklyClosed_conj_of_muIsoS4 hPG htr hd.hW hd.hS4
  exact ⟨S₀, hwc⟩

theorem exists_mem_conj_of_le (hc : P23Cfg n Y R S t K' W u e g) {H : Subgroup Y} (hWH : W ≤ H) {y : Y}
    (hyH : conjSub y W ≤ H) : ∃ c ∈ H, conjSub c W = conjSub y W := by
  obtain ⟨S₀, hwc⟩ := exists_weaklyClosed_of_cfg hc
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hc.data.hW
  obtain ⟨c, hcH, hc'⟩ := hwc.exists_mem_mul hW2 hWH hyH
  refine ⟨c⁻¹, H.inv_mem hcH, ?_⟩
  have h1 : conjSub y W = conjSub c⁻¹ (conjSub (c * y) W) := by
    rw [← conjSub_mul, inv_mul_cancel_left]
  rw [h1, hc']

theorem exists_rLayer_conj (hc : P23Cfg n Y R S t K' W u e g) {d : Y}
    (hde : d ∈ Subgroup.centralizer ({e} : Set Y)) :
    ∃ x ∈ rLayer (Om R) e, conjSub x W = conjSub d W := by
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hWE := w_le_rLayer hc
  have hdE : conjSub d W ≤ rLayer (Om R) e := by
    have h := conjSub_mono (n := d) hWE
    rwa [conjSub_rLayer_eq hΩ hde] at h
  exact exists_mem_conj_of_le hc hWE hdE

theorem p23E8AWFib_proved : P23E8AWFib n := by
  intro _ _ Y _ _ R S t K' W u e g hc _ _ _ _ d hd
  exact exists_rLayer_conj hc hd.2

end AWFib

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWF
