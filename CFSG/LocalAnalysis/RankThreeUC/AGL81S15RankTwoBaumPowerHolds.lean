module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumCases
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoK543
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541DynkinA2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumHolds

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem k517_4b_baumPower_A2B2G2 :
    K517_4b_baumPower_A2B2G2 :=
  K517_4b_baumPower_A2B2G2_of_cases
    (K517_4b_baumPower_A2_of_identification
      (fun _ _ _ _ _ _ hX hGood _ hY _ _ hrt hA ⟨e⟩ _ hq hdvd =>
        nonempty_mulEquiv_sl3_of_gnYComponent_A2 hX hGood hY hrt hA e hq hdvd)
      k541DynkinA2)
    (K517_4b_baumPower_B2_of_K543DynkinB2 k543DynkinB2) k517_4b_baumPower_G2

end CFSG.LocalAnalysis.RankThreeUC.S15

end
