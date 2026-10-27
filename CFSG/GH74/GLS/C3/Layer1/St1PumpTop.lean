module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.GLS.C3.Layer1.St1PumpClass
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH1

public section

namespace CFSG.GH74.GLS

open C3.Layer1.PumpCalc

theorem b_st1_prop51_pumpup_h2_proved
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) : B_st1_prop51_pumpup_h2 := by
  intro G _ _ hC3 hN T7 P41 x y K R hu hstar hR hyR h2
  exfalso
  have hC2 : C2Facts :=
    ⟨fun L _ _ hP hC hU hno => C3.Layer1.PumpClass.c2_u2_fm9 hG hF hP hC hU hno,
      fun L _ _ hP hC hcen S _ _ hS hno e =>
        e.elim fun e => C3.Layer1.PumpClass.not_inU2_quotient_of_centre hG hF hP hC hcen hS hno e⟩
  have hU2 : ∀ (z y : G) (J : Subgroup G), IsUnbalancingTriple z y J →
      InU2 (kBar J) ∧ ¬ IsL34Quotient (kBar J) := by
    intro z y J hzyJ
    have hU : InU2 (kBar J) := h102 G hC3 z y J hzyJ.isLocallyUnbalancing
    refine ⟨hU, fun hl34 => ?_⟩
    exact hL34 G hC3.gen4 z J hzyJ.1.1 hzyJ.1.2 ⟨hl34, (inU2_center hU).1, (inU2_center hU).2⟩
  have hL29 : ∀ (z y : G) (J : Subgroup G), IsTerminallyUnbalancing z y J →
      pRank 2 ↥(CxK z J) = 1 := fun z y J h =>
    (terminallyUnbalancing_L29 h102 h14 hL34 IVK.Proofs2.b_ivk_rank_add_L29 hC3 hN P41 h).2.2.2
  exact no_unbalancing_triple_of_rank_two hC3.pRank_eq_four hC3.gen4 T7 hC2 hU2 hL29 hu h2

end CFSG.GH74.GLS
