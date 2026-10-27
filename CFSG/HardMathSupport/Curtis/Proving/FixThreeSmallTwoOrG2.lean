module

public import CFSG.HardMathSupport.Curtis.Proving.FixThreeSmallFour
public import CFSG.HardMathSupport.Curtis.Proving.A8FixThree

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.AGLEmbedding

theorem fixThreeVoid_isSmallTwoOrG2 :
    FixThreeVoid IsSmallTwoOrG2 := by
  intro Y _ _ L J u h hX
  rcases (isSmallTwoOrG2_iff _).1 hX with h4 | h8
  · exact fixThreeVoid_smallFour Y L J u h h4
  · exact fixThreeVoid_altEight Y L J u h h8

end CFSG.HardMathSupport.Curtis.Proving

end
