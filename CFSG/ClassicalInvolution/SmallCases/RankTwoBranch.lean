module

public import CFSG.ClassicalInvolution.SmallCases.Partition
import CFSG.ClassicalInvolution.RankTwo

public section

namespace CFSG.ClassicalInvolution

theorem citRankTwo : CITRankTwo := fun F _ _ _ hnab z hz K hzK hK hw hns h2 =>
  oddLieType_or_m11_of_twoRank_le_two F hnab h2 z hz K hzK hK hw hns

theorem citSimplePerfect_of_cases' (hF : CITFrameRankFour) (h1 : CITSectionalFour) (h2 : CIT2A7)
    (h3 : CITDisconnected) (h4 : CITConnectedA2) (h5 : CITTypeC) : CITSimplePerfect :=
  citSimplePerfect_of_cases hF citRankTwo h1 h2 h3 h4 h5

end CFSG.ClassicalInvolution
