module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddGoodProof
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3Dickson

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

theorem overgroupL32U3Odd_proved : OvergroupL32U3Odd :=
  overgroupL32U3Odd_of_dickson fun K _ _ p f _ hK _ hq3 hq4 A H hA _ hAH =>
    psl2_normalizer_three_dichotomy hK hq3 hq4 hA hAH

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
