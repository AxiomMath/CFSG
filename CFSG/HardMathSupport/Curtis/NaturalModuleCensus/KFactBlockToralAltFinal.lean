module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusWire
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.Main

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.AGLEmbedding

theorem kFactBlockToralAlt (hGA : CFSG.Open.GriessAllModelsStatement) : KFactBlockToralAlt :=
  kFactBlockToralAlt_of_plusD hGA (altPlusCellD hGA)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
