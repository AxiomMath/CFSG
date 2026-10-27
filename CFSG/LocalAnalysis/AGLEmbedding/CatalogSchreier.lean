module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.AGLEmbedding

theorem kFactCatalogSchreier_holds :
    KFactCatalogSchreier := by
  intro K _ _ hs hna hcat
  haveI := hs
  exact CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds K hna hcat

end CFSG.AGLEmbedding
