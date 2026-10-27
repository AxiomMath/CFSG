module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCore
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BWit
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BWitM
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BWitFi24
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BWitSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDist
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDistM
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo1Row
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BSuzRow
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyRow
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo1U
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BSuzU
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BRowTh
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMRows
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveRankHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2Row
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BRowFi24

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B


theorem i301BAt_holds

    : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), S8.L89.I301BAt G p := by
  have h : I301BRes :=
    { rowLy := rowLy_holds
      rowCo2 := rowCo2_holds
      rowCo1 := rowCo1_holds uCo1
      rowFi24 := rowFi24_holds
      rowSuz := rowSuz_holds uSuz
      rowTh := rowTh_holds
      rowM3 := rowM3_holds
      rowM5 := rowM5_of_leB5 H1017.twoRankLe_five_B
      distLy := distLy_holds
      distCo2 := distCo2_holds
      distCo1 := distCo1_holds
      distFi24 := distFi24_holds
      distSuz := distSuz_holds
      distTh := distTh_holds
      distM3 := distM3_holds
      distM5 := distM5_holds
      witLy := witLy_holds
      witCo2 := witCo2_holds
      witCo1 := witCo1_holds
      witFi24 := witFi24_holds
      witFi24Cover := witFi24Cover_holds
      witSuz := witSuz_holds
      witSuzCover := witSuzCover_holds
      witTh := witTh_holds
      witM3 := witM3_holds
      witM5 := witM5_holds
      leB3 := twoRankLe_three_B
      leB5 := H1017.twoRankLe_five_B }
  intro G _ _ p hp hp2 a y J Bs I K R0 row ha _ hodd hJ hprow hJcat hBs hBsX hBscard hb hy hI
    hIrow hR0y hR0 hd hKR0 hK hR0card R1 hR1X hR1 hKR1 hR01
  refine i301B_core CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
    h hp hp2 ha hodd hJ hprow hJcat hBs hBsX hBscard hb hy hI hIrow hR0y
    hR0 ?_ hKR0 hK hR0card hR1X hR1 hKR1 hR01
  rcases hd with rfl | hd
  · rw [show K = ⊥ from hK]
    exact bot_le
  · exact le_sup_of_le_left (hd.1.trans ((S8.L89.glaPLayer_le p _).trans inf_le_left))

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
