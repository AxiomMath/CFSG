module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15FactorX1
public import CFSG.Quasithin.H13.NQS1312H
public import CFSG.Quasithin.H13.LocDblCriterion
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSetup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.McLaughlin

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem gnSetting_borelPre_of_noXBlock (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hNB : ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False) :
    GNSetting (borelPre T Ls) (T.subgroupOf (borelPre T Ls)) where
  kGroup := CFSG.IsKGroup.subgroup hX.kGroup (borelPre T Ls)
  sylow := CFSG.Quasithin.H13.LocDbl.isSylowTwoOf_subgroupOf_top
    (CFSG.Quasithin.H13.U3.NLine.isSylowTwoOf_of_le_top hX.sylow (t_le_borelPre hX))
  charTwo := charTwo_top_of_le hX.charTwo
    ((CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow).trans (t_le_borelPre hX))
    le_top
  noXBlock := hNB

end CFSG.LocalAnalysis.RankThreeUC.S15
