module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylowData

public section

namespace CFSG.AGLEmbedding.D4Two

open CFSG.Quasithin

@[expose] def sylowGroup : Subgroup (GL (Fin 8) GF8) :=
  Subgroup.closure {wordGL wordA, wordGL wordB}

end CFSG.AGLEmbedding.D4Two
