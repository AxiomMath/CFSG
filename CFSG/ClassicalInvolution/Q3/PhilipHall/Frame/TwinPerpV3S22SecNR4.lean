module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22SecNR3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ATr3
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLieNR

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Uniform


theorem secTwinNoRoot_of {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) :
    SecTwinNoRoot n := by
  intro X _ _ hlt Φ hS htrans hdisc hno A hA B hB x hxA hxB α hαA hαB
  obtain ⟨h2', hl, hex⟩ := TwinDisc.lifts_of_noExit hP hlt hS hno
  obtain ⟨L, u, hL⟩ := hl A hA
  obtain ⟨L', u', hL'⟩ := hl B hB.1
  have hu : u = x := hL.inv.eq hxA
  have hu' : u' = x := hL'.inv.eq hxB
  rw [hu] at hL
  rw [hu'] at hL'
  have hO : Balance.oddCoreIn (Subgroup.centralizer ({x} : Set X)) = ⊥ := (hno A hA x hxA).1
  have hAmem := satU_mem_liftFam hA hL
  have hBmem := satU_mem_liftFam hB.1 hL'
  have hxA' : IsUniqueInvolution (satU (.sl2 3 1) L x) x :=
    isUniqueInvolution_liftFam_of_le hAmem hxA hL.le_sat
  have hxB' : IsUniqueInvolution (satU (.sl2 3 1) L' x) x :=
    isUniqueInvolution_liftFam_of_le hBmem hxB hL'.le_sat
  have hBnbr : satU (.sl2 3 1) L' x ∈ omegaNbr (liftFam Φ) (satU (.sl2 3 1) L x) :=
    (hex.mem_omegaNbr_liftFam_iff hS.hyp h2' hl hAmem hA hL.le_sat hBmem hB.1 hL'.le_sat).mpr hB
  have hne : Φ.Nonempty := ⟨A, hA⟩
  have hΛ : HypOmegaModU (.sl2 3 1) (liftFam Φ) := hypOmegaModU_liftFam hS.hyp.conjInvariant
  have hgenΛ : omegaGen (liftFam Φ) = ⊤ :=
    (inClass3_liftFam hS.hyp.conjInvariant hne hl hS.gen).generated
  have hAΛ := ExactSylow.aEmpty_liftFam hS.hyp h2' hl hex hS.aEmpty
  have hdiscΛ : ¬ T3.DStarConnected (liftFam Φ) := fun hc =>
    hdisc (TwinDisc.dstarConnected_of_liftFam hS.hyp h2' hl hex hc)
  have htr₀ := liftFam_trans hS.hyp hAmem hL.le_sat (fun J' hJ' => htrans A hA J' hJ')
  have htransΛ : ∀ K ∈ liftFam Φ, ∀ M ∈ liftFam Φ, ∃ g : X, conjSub g K = M := by
    intro K hK M hM
    obtain ⟨g, hg⟩ := htr₀ K hK
    obtain ⟨g', hg'⟩ := htr₀ M hM
    exact ⟨g' * g⁻¹, by rw [conjSub_mul, ← hg, conjSub_inv_conjSub, hg']⟩
  have hfixL := lift_fix_of_fix hS.hyp hA (h2' A hA) hL hO α hαA
  have hfixL' := lift_fix_of_fix hS.hyp hB.1 (h2' B hB.1) hL' hO α hαB
  rw [satU_eq_of_oddCoreIn_eq_bot (L := L) hO] at hxA' hBnbr hAmem
  rw [satU_eq_of_oddCoreIn_eq_bot (L := L') hO] at hxB' hBnbr hBmem
  exact SecNR.sq_noRoot_of_twin_pair
    ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr hcit) hlt hΛ hS.oddFree hgenΛ
    hAΛ htransΛ hdiscΛ hAmem hBnbr hxA' hxB' α hfixL hfixL'

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
