module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusA.Main

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.AGLEmbedding

theorem kFactBlockToralAlt_of_plusD (hGA : CFSG.Open.GriessAllModelsStatement)
    (hD : AltPlusCellD) : KFactBlockToralAlt :=
  kFactBlockToralAlt_of_plus hGA (altPlusCell_of (altPlusCellA hGA) hD)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
