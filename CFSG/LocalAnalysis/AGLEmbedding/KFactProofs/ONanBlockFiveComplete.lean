module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockFiveMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycG2

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.BlockCyc


theorem kFactBlockFiveNoncyclic_of_asc81b (h93 : Asc81bNineThree) (h86 : Asc81bEightSix)
    (hGA : CFSG.Open.GriessAllModelsStatement) : KFactBlockFiveNoncyclic :=
  kFactBlockFiveNoncyclic_of_lie lieCyclicG2 h93 h86 hGA

end CFSG.AGLEmbedding
