module

public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.GH74.GLS.C3.Layer1.BackLeaves

public section

namespace CFSG.GH74.GLS

theorem s_lemma114_of (h : B_lemma114_nonEven) : S_lemma114 := by
  intro G _ _ hG x K L M T Q hh p91 l113
  by_cases hE : IsEvenType G
  · exact hE.2.1 x hh.a.orderOf_x
  · exact h G hG hE x K L M T Q hh p91 l113

end CFSG.GH74.GLS
