module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbAltTen
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbVoidCited
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDefs

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.Open CFSG.QuasithinUnique

theorem blockIbRankRest_of_cited (h85 : Asc81bEightFive)
    (hT : CitedBlockTransvectionPLType) : BlockIbRankRest := by
  intro G _ _ M S L D x h h2 E hEL hEP hED hEab hE9 t ht htE htF
  rcases nineThree_rest_of_not_two h h2 with h3 | h4 | h5 | h6 | h7 | h8
  · exact (false_of_nineThreeThree h85 hT h h3).elim
  · exact (false_of_nineThreeFour h h4).elim
  · exact (false_of_nineThreeFive h85 h h5).elim
  · exact blockIbRank_nineThreeSix_or_Seven h (Or.inl h6) E hEL hEP hED hEab hE9 t ht htE htF
  · exact blockIbRank_nineThreeSix_or_Seven h (Or.inr h7) E hEL hEP hED hEab hE9 t ht htE htF
  · exact (false_of_nineThreeEight h h8).elim

theorem blockIbAbRest_of_cited (h85 : Asc81bEightFive)
    (hT : CitedBlockTransvectionPLType) : BlockIbAbRest := by
  intro G _ _ M S L D x h h2 U hUL hUP hUD hU3
  rcases nineThree_rest_of_not_two h h2 with h3 | h4 | h5 | h6 | h7 | h8
  · exact (false_of_nineThreeThree h85 hT h h3).elim
  · exact (false_of_nineThreeFour h h4).elim
  · exact (false_of_nineThreeFive h85 h h5).elim
  · exact blockIbAb_nineThreeSix_or_Seven h (Or.inl h6) U hUL hUP hUD hU3
  · exact blockIbAb_nineThreeSix_or_Seven h (Or.inr h7) U hUL hUP hUD hU3
  · exact (false_of_nineThreeEight h h8).elim

end CFSG.HardMathSupport.Curtis.UnitaryLevi
