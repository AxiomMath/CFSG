module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420MainA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporCardRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeM3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Co1RowB
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyMain
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Co1RowSpor
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Co1RowLA
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Co1RowSuz

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.HardMathSupport.Solomon.Coordinator (sporadicOrdersTable_holds lieOrderBridge_holds)
open CFSG.LocalAnalysis.GLTheoremA (kdChevDownQ_three_of_lieComp lieComp_holds kdAltDown_holds)
open CFSG.LocalAnalysis.GLTheoremA.K14Spor (cardRow_fi22' cardRow_fi23' cardRow_fi24')


theorem i1420Co1A_holds
    : I1420Co1A := by
  have hOrd := sporadicOrdersTable_holds
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hSimple : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .Suz).Group :=
    (MulEquiv.isSimpleGroup_congr (hbr .Suz).some).1 CFSG.Sporadic.Suz.isSimpleGroup_Suz
  have hSuz := typeHyp3_suz_of_facts hOrd hOut hSimple
  refine i1420RowA_of_branches Nat.prime_three ?_ ?_ ?_
  · intro S _ _ idx e β J h
    exact co1Row_lie_of_facts hOrd lieOrderBridge_holds
      (fun q => kdChevDownQ_three_of_lieComp lieComp_holds q) idx e h
  · intro S _ _ n hn e β J h
    exact co1Row_alt_of_facts hOrd kdAltDown_holds hn e h
  · intro S _ _ t e β J h
    exact co1Row_spor_of_rows hOrd hOut
      (cardRow_fi22' hOut hbr (by decide +kernel)) (cardRow_fi23' hOut hbr (by decide +kernel))
      (cardRow_fi24' hbr hOut (by decide +kernel) (by decide +kernel))
      (cardRow_B_of_seven_dvd hOut (by decide +kernel) (by decide +kernel))
      (BMType.typeRow3_M hSuz 17 (by norm_num) (by norm_num) (by norm_num)
        31 (by norm_num) (by norm_num) (by norm_num))
      S t e β J h

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
