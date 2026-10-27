module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Final
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_RedDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i112Red_of_tables (T : Tables112) (TL : TableL2) : I112Red := by
  intro X _ _ hX p hp hp2 hO B hB hr L hL hnL
  obtain ⟨hidx, hz, -⟩ := i112_ok_of_tables T hX hp hp2 hO hB hr hL hnL
  rcases hz with ⟨hc1, hp3, hm, hw⟩ | ⟨hp3, hc3⟩
  · subst hp3
    refine ⟨rfl, hidx, Or.inr ?_⟩
    exact TL.T ↥L (i116e_isQuasisimple hO hL) (isKGroup_of_le hX L) hc1 hm hw
  · refine ⟨hp3, hidx.trans hp3, Or.inl fun h => ?_⟩
    have := Subgroup.card_bot (G := ↥L)
    rw [← h, hc3] at this
    omega

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
