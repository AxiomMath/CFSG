module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.AGLEmbedding

theorem kFactCatalogSchreier :
    KFactCatalogSchreier := by
  intro K _ _ hs hnonab hK
  have := hs
  exact RankThree.PartOne.TCB.schreierFor_inCatalog_holds K hnonab hK

end CFSG.AGLEmbedding
