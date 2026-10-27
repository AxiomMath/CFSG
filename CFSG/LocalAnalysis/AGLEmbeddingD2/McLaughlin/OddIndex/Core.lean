module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreMain
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreModFix

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem lThreeTwoCoreOdd_of (hS : CFSG.AGLEmbedding.CatalogOuterSolvable) : LThreeTwoCoreOdd :=
  lThreeTwoCoreOdd_of_modFix hS fun _ _ _ _ hY ha => modFix hY ha

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
