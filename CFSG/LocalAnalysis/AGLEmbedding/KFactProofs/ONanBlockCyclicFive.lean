module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycMain

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding CFSG.AGLEmbedding.BlockCyc

theorem kFactBlockCyclicThreeFive_of_lie (h93 : Asc81bNineThree) (hP : LieCyclicParabolic)
    (hO : LieCyclicOrthogonal) : KFactBlockCyclicThreeFive := by
  intro G _ _ M S L hK hA hL hX hS h3 V hVN hV
  exact blockCyclicFive_of_lie h93 hP hO hK hA hL hX hS h3 V hVN hV

end CFSG.AGLEmbeddingD2
