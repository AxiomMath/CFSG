module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VBarLayer
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VSylow
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma210

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem lemma210_input11_2Struct_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) : Lemma210Ns.Input11_2Struct := by
  intro G _ _ m hS X B L hB hBX hr hL hnL htype
  obtain ⟨hp, -, -, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ := i112v_bar hS hB hBX hr hL hnL
  obtain ⟨-, -, -, -, -, hcase⟩ :=
    i112v_core T TL TT TM hQK hp (by norm_num) hQcore hBel hrankQ hLbar hnLQ
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp hL.1 hL.2.1
  have hq' : CFSG.Open.IsQuasisimple ↥(barX 3 X L) := i116e_isQuasisimple hQcore hLbar
  have hK' : CFSG.Open.IsKGroup ↥(barX 3 X L) := isKGroup_of_le hQK _
  have ht' : IsHatSix ↥(barX 3 X L) ∨ IsHatSeven ↥(barX 3 X L) ∨
      IsHatMTwentyTwo ↥(barX 3 X L) ∨ IsSLThreeExc ↥(barX 3 X L) ∨
      IsSUThreeExc ↥(barX 3 X L) := by
    rcases htype with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (i112f_isSLThreeExc_of_mulEquiv e h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (i112f_isSUThreeExc_of_mulEquiv e h))))
  have hsyl' := TM.T10_10S _ hq' hK' ht'
  have hsyl := i112v_sylow_facts_of_mulEquiv e hsyl'
  have hZ3' : Nat.card (Subgroup.center ↥(barX 3 X L)) = 3 := by
    rcases hcase with ⟨-, -, hm1, -⟩ | ⟨h3, -⟩
    · exfalso
      obtain ⟨hc, hna, hexp⟩ := hsyl' default
      have := i112v_two_le_pRank_of_sylow default hc hna hexp
      omega
    · exact h3
  have hZ3 : Nat.card (Subgroup.center (barOf 3 L)) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hZ3'
  refine ⟨fun b₀ hb₀ hb₀n => ?_, fun R => ?_⟩
  · obtain ⟨hs, hdvd, ⟨e₁⟩⟩ := i112v_barLayer T TL TT TM hS hB hBX hr hL hnL hb₀ hb₀n
    have := hs
    have hO := i112v_glaPPrimeCore_eq_bot hp hdvd
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans (QuotientGroup.quotientBot.trans
      (e₁.trans (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm))))⟩
  · obtain ⟨hc, hna, -⟩ := hsyl R
    have hna' : ∃ r s : ↥(R : Subgroup (barOf 3 L)), r * s ≠ s * r := by
      obtain ⟨r, hr, s, hs, h⟩ := hna
      exact ⟨⟨r, hr⟩, ⟨s, hs⟩, fun h' => h (congrArg Subtype.val h')⟩
    exact ⟨⟨hc, i112v_card_center_eq_three hc hna', i112v_commutator_eq_center hc hna'⟩,
      (i112v_sylow_center hZ3 R hc hna).2⟩

end CFSG.HardMathSupport.Solomon.Coordinator
