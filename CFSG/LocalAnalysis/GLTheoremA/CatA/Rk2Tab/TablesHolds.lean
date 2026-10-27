module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Tables
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Split
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerTwDOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerTwE6Three
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperTwA5Full

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open


theorem rk2Lower_holds : Rk2Lower :=
  rk2Lower_of rk2_low_twd_one rk2_low_twe6_three

theorem rk2Upper_holds : Rk2Upper :=
  rk2Upper_of CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    (fun K _ _ lab hK ht hn hc =>
      rk2_up_twa5_full CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
        (twoLocalPrimeRank_statedSU_quot_le_of_dvd 3 Nat.prime_three (by norm_num))
        hK ht hn hc)
    rk2TwE6LeviRankInputMaximal_holds

theorem rk2Tables_holds : Rk2Tables :=
  rk2Tables_of rk2Lower_holds rk2Upper_holds rk2Split_holds

end CFSG.LocalAnalysis.GLTheoremA
