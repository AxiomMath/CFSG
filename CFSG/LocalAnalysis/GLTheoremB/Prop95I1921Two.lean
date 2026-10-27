module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Six

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

theorem input19_21_2_holds (hH : HatSevenOddInverts) :
    Input19_21_2 := by
  intro X _ _ p hp hp2 K hK hO hAlt D Sd hD hC So hSo _
  obtain ⟨-, n, hn, ⟨e⟩⟩ := hAlt
  by_cases hn6 : n = 6
  · subst hn6
    rcases input19_21_2_six hp hp2 hK hO e hD hC hSo with h | ⟨h5, hc2, hpgl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨⟨e⟩, h5, hc2, hpgl⟩))
  · rcases input19_21_2_ne6 hH hp hp2 hK hO hn hn6 e hD hC hSo with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
