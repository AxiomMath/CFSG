module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VBar
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma26
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem input11_2One_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) : Lemma26Ns.Input11_2One := by
  intro G _ _ m p hS X B L hB hBX hr hL hnL
  obtain ⟨hp, hp2, -, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ := i112v_bar hS hB hBX hr hL hnL
  obtain ⟨h3, hrel, -, -, -, hcase⟩ :=
    i112v_core T TL TT TM hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  subst h3
  have e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp hL.1 hL.2.1
  have hJ : barX 3 X (bClosure B L) = i112J (barX 3 X B) (barX 3 X L) :=
    i112f_barX_bClosure hBX hL.1
  have hBp : IsPGroup 3 B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  refine ⟨rfl, (i112f_relIndex_barX hL hBX).symm.trans hrel, ?_⟩
  rw [hJ]
  rcases hcase with ⟨-, -, -, hL2⟩ | ⟨-, ht5, h3' | ⟨h9, hSU, hC, hrk⟩⟩
  · exact Or.inl (i112f_isLTwoOddPow_of_mulEquiv e.symm hL2)
  · refine Or.inr (Or.inl ⟨?_, i112v_exc_of_mulEquiv e.symm ht5⟩)
    rw [i112f_card_center]
    exact h3'
  · refine Or.inr (Or.inr ⟨?_, i112v_isSUThreeTwoPow_of_mulEquiv e.symm hSU, ?_, ?_⟩)
    · rw [i112f_card_center]
      exact h9
    · rw [map_subtype_center]
      exact hC
    · rw [← rank_barX_of_isPGroup hp hBp hBX]
      exact hrk

end CFSG.HardMathSupport.Solomon.Coordinator
