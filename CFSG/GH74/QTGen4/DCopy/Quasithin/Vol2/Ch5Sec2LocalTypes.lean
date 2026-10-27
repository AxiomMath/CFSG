module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalTypes
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt5_2_9_of_F4 (h527 : Stmt5_2_7_F4) (h528 : Stmt5_2_8_F4) : Stmt5_2_9_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have h2n : 2 ≤ n := hyp.two_le
  obtain ⟨htype, -, -⟩ := h527 G T M L V H B D L₂ n hyp
  rcases h528 G T M L V H B D L₂ n hyp with hK | ⟨hA, K', hlt, hK', -⟩
  · rcases htype with (h | h | h | h | h) | ⟨m, hm, h2, hU⟩ | ⟨h4, hU⟩
    · exact Or.inl ⟨n, h2n, Or.inl ⟨h, hK⟩⟩
    · exact Or.inl ⟨n, h2n, Or.inr (Or.inl ⟨h, hK⟩)⟩
    · exact Or.inl ⟨n, h2n, Or.inr (Or.inr (Or.inl ⟨h, hK⟩))⟩
    · exact Or.inl ⟨n, h2n, Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hK⟩)))⟩
    · exact Or.inl ⟨n, h2n, Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hK⟩)))⟩
    · exact Or.inr (Or.inl ⟨m, hm, h2, hU, hK⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hU, hK⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hA, not_isMaximalLocal_of_lt hlt hK'⟩))

end CFSG.Quasithin.H13
