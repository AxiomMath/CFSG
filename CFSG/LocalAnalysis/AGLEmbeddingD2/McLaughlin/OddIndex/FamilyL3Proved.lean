module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.GL2Nonsplit

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

theorem overgroupL32L3_proved : OvergroupL32L3 :=
  overgroupL32L3_of_max fun _ _ _ hq h5 => gl2NonsplitMax_of_mod hq h5

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
