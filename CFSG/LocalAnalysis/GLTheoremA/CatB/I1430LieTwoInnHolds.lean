module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnRed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxAll
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnOrthD4
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnLin
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnOrth
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnExc
import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Odd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.Sec4.Ronan148L (excRationalLieTypes_holds)


theorem i1430LieTwoInn_holds : I1430LieTwoInn :=
  i1430LieTwoInn_of_families LieSemisimple.lieSemisimpleCent lieOrderBridge_holds
    (fun d hd => KD264Lie.lieCompIdx_all d 3 Nat.prime_three (by norm_num)
      (fun h3 => absurd (h3.trans hd) (by norm_num)) trivial)
    i1430InnNoA_proved i1430InnNoTwistedA_proved i1430InnNoD_proved i1430InnNoTwistedD_proved
    (i1430InnNoE_proved LieSemisimple.lieSemisimpleCent excRationalLieTypes_holds)
    (i1430InnNoTwistedE6_proved LieSemisimple.lieSemisimpleCent excRationalLieTypes_holds)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
