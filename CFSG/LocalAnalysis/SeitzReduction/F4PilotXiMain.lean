module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLProof

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)
open CFSG.Quasithin (perfectCore)

section CaseL

theorem e6RowXiCaseLInput_holds : E6RowXiCaseLInput := by
  intro G _ _ L K _ _ _ e t f hw hf _ K' _ _ hK' e₀ M hM htM eM η hη hx φ hφ w hwM hwL _ _ hwx
    hwΛ hcomm _ _ htN htwN _ hψ hφ'
  obtain ⟨ψ, hψ⟩ := hψ
  obtain ⟨φ', hφ'⟩ := hφ'
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hLG₀ := le_pieceSpan hq e
  have hG₀ := commutator_pieceSpan e
  have h36 : 2 ^ (36 * f) ∣ Nat.card (adjointGroup TwistTag.E6.tag K') := by
    change 2 ^ (36 * f) ∣ Nat.card (adjointGroup Tag.E6 K')
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hK']
    obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordE6' (by omega : 1 ≤ f)).two
    rw [hr, mul_comm 36 f]
    exact Dvd.intro r rfl
  have htC : t ∉ centralizer (pieceSpan e : Set G) :=
    not_mem_centralizer_of_two_pow_dvd_quot hw.standard hw.one_le hw.card_eq e
      hw.mem_centralizer hw.orderOf_eq hG₀ e₀ h36
  have hZ := odd_card_center_of_odd_card_centralizer (odd_card_centralizer_pieceSpan hw e hLG₀ htC)
  have hZM : Odd (Nat.card (center M)) := by
    obtain ⟨g, rfl⟩ := hM
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  have hΛL := perfectCore_inf_centralizer_le hw.standard (isSolvable_outer_of_mulEquiv_F4 e)
    hw.mem_centralizer hw.orderOf_eq M
  have := charP_two_of_natCard_eq_two_pow hK'
  obtain ⟨J, eJ, hmod⟩ := exists_xiCaseLModel_E6 hf hK' hη hx
  exact false_of_caseL_model hf hw.card_eq e hw.center_eq_bot hw.orderOf_eq hw.mem_centralizer
    hK' hmod e₀ htN hψ hZM eM htM hφ hΛL hwM hwL hwx hwΛ hcomm htwN hφ'

theorem twistedE6RowXiCaseLInput_holds : TwistedE6RowXiCaseLInput := by
  intro G _ _ L K _ _ _ e t f hw hf _ K₂ _ _ σ hK₂ hσ e₀ _ M hM htM eM η hη hx φ hφ w hwM hwL _ _
    hwx hwΛ hcomm _ _ htN htwN _ hψ hφ'
  obtain ⟨ψ, hψ⟩ := hψ
  obtain ⟨φ', hφ'⟩ := hφ'
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hLG₀ := le_pieceSpan hq e
  have hG₀ := commutator_pieceSpan e
  have h36 : 2 ^ (36 * f) ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K₂ σ) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two (by omega) hK₂ σ hσ]
    obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordTwistedE6' (by omega : 1 ≤ f)).two
    rw [hr, mul_comm 36 f]
    exact Dvd.intro r rfl
  have htC : t ∉ centralizer (pieceSpan e : Set G) :=
    not_mem_centralizer_of_two_pow_dvd_quot hw.standard hw.one_le hw.card_eq e
      hw.mem_centralizer hw.orderOf_eq hG₀ e₀ h36
  have hZ := odd_card_center_of_odd_card_centralizer (odd_card_centralizer_pieceSpan hw e hLG₀ htC)
  have hZM : Odd (Nat.card (center M)) := by
    obtain ⟨g, rfl⟩ := hM
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  have hΛL := perfectCore_inf_centralizer_le hw.standard (isSolvable_outer_of_mulEquiv_F4 e)
    hw.mem_centralizer hw.orderOf_eq M
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have := charP_two_of_natCard_eq_two_pow hk
  have : Finite (GaloisField 2 f) := finite_of_natCard_eq_two_pow hk
  obtain ⟨J, eJ, A, hmod⟩ := exists_xiCaseLModel_twistedE6 hf hK₂ hσ hη hx
  exact false_of_caseL_model hf hw.card_eq e hw.center_eq_bot hw.orderOf_eq hw.mem_centralizer
    hk hmod e₀ htN hψ hZM eM htM hφ hΛL hwM hwL hwx hwΛ hcomm htwN hφ'

end CaseL

end CFSG.SeitzReduction.F4Pilot
