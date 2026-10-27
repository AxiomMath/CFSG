module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.YS03Goals
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KD1913Aut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD2027
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD91
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147c
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Chev
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Lie
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I1426
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I147
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I1912
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I1913
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I2027
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KDM12Holds
public import CFSG.LocalAnalysis.GLTheoremA.S4S.M12
public import CFSG.LocalAnalysis.GLTheoremA.S4S.YS03Schreier

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

theorem ys03_of_kdata_K
    (h145 : GWLBalanceClause3)
    (h1 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD1912Chev p) (h2 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD1912Two p)
    (h13 : KD1913) (h27 : KD2027) (h264 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264K p) (h91 : KD91)
    (h147 : KD147) (hM : KDM12) (h1426 : KD1426Cat) : YS03 :=
  ys03_of_schreier (CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog) h145 (i1912At_of h1 h2)
    (i1913At_of h13) (i2027At_of h27) fun G _ _ m _ p hp =>
      ⟨i264At_of_K (h264 p hp.1.1 hp.1.2.1), i91At_of h91, i147At_of h147, i1016At_of hM,
        i71M12At_of hM, i1426At_of h1426⟩

theorem ys03_of_kdata_rest2K
    (hL3 : KD1912TwoLie 3) (hL5 : KD1912TwoLie 5) (hL13 : KD1912TwoLie 13)
    (h264 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264K p) (h1426 : KD1426Cat) : YS03 :=
  ys03_of_kdata_K (gwLBalanceClause3_of_statement CFSG.Yardstones.Md42047359a2a.lBalance_of_goals)
    (fun p hp hp2 => kd1912Chev_holds hp hp2)
    (fun p hp hp2 => kd1912Two_of_parts hp hp2 (kd1912TwoLie_all hL3 hL5 hL13 p))
    (kd1913_of CatB.kd1913MathieuAut_holds) kd2027_holds h264 kd91_holds kd147_holds kdM12_holds
    h1426

theorem ys03_of_kdata_rest3K
    (hL2 : KD1912TwoL2) (hL3 : KD1912TwoL3) (hU3 : KD1912TwoU3) (hR3 : KD1912TwoRows3)
    (hR5 : KD1912TwoRows5) (hL33 : KD1912TwoL33)
    (h264 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264K p) (h1426 : KD1426Cat) : YS03 :=
  ys03_of_kdata_rest2K (kd1912TwoLie_three hL2 hL3 hU3 hR3) (kd1912TwoLie_five hR5)
    (kd1912TwoLie_thirteen hL33) h264 h1426

end CFSG.LocalAnalysis.GLTheoremA
