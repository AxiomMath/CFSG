module

public import CFSG.LieType.SeitzGeneration.ConsumerD2Narrow

public section

namespace CFSG.AGLEmbeddingD2

theorem d2SeitzCross_of_lowN (hLowN : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoLowN) :
    D2SeitzCross :=
  fun _ _ _ _ _ _ _ _ hK d ⟨e⟩ hp hex => hK.false_of_seitzLowN hLowN d e hp hex

end CFSG.AGLEmbeddingD2
