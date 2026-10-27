module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Final
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCell
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.TwistedA

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding


theorem kFactBlockToralAltIb (hSch : KFactCatalogSchreier)
    (hGA : CFSG.Open.GriessAllModelsStatement) : KFactBlockToralAltIb :=
  kFactBlockToralAltIb_of_cells hSch hGA (LinCell.altIbCell_a hSch hGA)
    (altIbCell_twistedA hSch hGA)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
