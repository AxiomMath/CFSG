module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSmallFour
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbAltEight

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.HardMathSupport.Curtis.Proving

section Small


theorem blockIbRankFam_small : BlockIbRankFam IsSmallTwoOrG2 := by
  intro Y _ _ Lb Pb D x hP hX hD E hEL hEP hED hEab hE9 t ht htE htF
  rcases (isSmallTwoOrG2_iff _).1 hX with h4 | h8
  · exact (blockIb_false_smallFour hP h4 hD).elim
  · obtain ⟨e⟩ := h8
    exact blockIb_altEight_rank hP e hD hEL hEP hE9

theorem blockIbAbFam_small : BlockIbAbFam IsSmallTwoOrG2 := by
  intro Y _ _ Lb Pb D x hP hX hD U hUL hUP hUD hU3
  rcases (isSmallTwoOrG2_iff _).1 hX with h4 | h8
  · exact (blockIb_false_smallFour hP h4 hD).elim
  · obtain ⟨e⟩ := h8
    exact blockIb_altEight_ab hP e hD hUL hUP hU3

end Small

end CFSG.HardMathSupport.Curtis.UnitaryLevi
