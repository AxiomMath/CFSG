module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporCoHe
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)


theorem cardRow_mcl_co1 (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    K14Spor.CardRow 898128000 .Co1 := by
  intro S _ _ e β hβ hβ1 J hJ hc
  have h := CFSG.HardMathSupport.Dickson.I271.TabCo1.grow_Co1_three hOut hbr S e
    Nat.prime_three (by norm_num) β hβ hβ1 J hJ
  rcases h with h | h | h <;> omega

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
