module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_RedDefs
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Core

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem noL2Reduced_of_cases (Tb : Tables113) (hmin : MinT113) (hjk : CaseJK113)
    (hjg : CaseJgt113) : NoL2Reduced := by
  intro Q _ _ hO B L hB hL hL2 hidx hall hmax hU hR1
  obtain ⟨S, hS, hS2, hBS⟩ := hU
  obtain ⟨T, hT, hT2, hBT, hTmin, hTel, hTcard⟩ := hmin Q B S hB hS hS2 hBS
  have hex : ∃ x ∈ B, x ∉ Subgroup.normalizer (L : Set Q) := by
    by_contra hcon
    push Not at hcon
    have h1 : B ≤ Subgroup.normalizer (L : Set Q) := fun b hb => hcon b hb
    rw [Subgroup.relIndex_eq_one.2 h1] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨x, hxB, hxn⟩ := hex
  have hc : Subgroup.center ↥L = ⊥ := (Tb.T0 ↥L hL2).2.2
  have hred : Red113 B L x T :=
    { tri := { elem := hB, comp := hL, center := hc, mem := hxB, not_mem := hxn, index := hidx }
      hO := hO, isL2 := hL2, hidx_all := hall, hmax := hmax, hR1 := hR1, T_ne := hT,
      T_two := hT2, T_norm := hBT, T_min := hTmin, T_elem := hTel, T_card := hTcard }
  by_cases hK : T ≤ Subgroup.normalizer ((t113K B L : Subgroup Q) : Set Q)
  · exact hjk Q B L x T hred hK
  · exact hjg Q B L x T hred hK

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
