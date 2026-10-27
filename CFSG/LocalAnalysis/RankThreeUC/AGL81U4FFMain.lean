module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFPartA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFPartBN
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFGrp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusN
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusO
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFPartBO

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

theorem partBN_stmt : PartBNStmt := by
  intro S _ _ hS n hn F _ _ hF L A ε ψ hεψ hA hAN
  exact partB_N hS hn hF ε ψ hεψ hA hAN

theorem kFactAGL81I54U4_of_inputs (hC : U4FFNatural) (hBO : PartBOStmt) (hBO4 : PartBO4Stmt)
    (hTN : TorusStepN) (hTO : TorusStepO) : KFactAGL81I54U4 :=
  kFactAGL81I54U4_of_abstract (partA_core hC partBN_stmt hBO hBO4 hTN hTO)

theorem kFactAGL81I54U4_of_partBO (hC : U4FFNatural) (hBO : PartBOStmt) (hBO4 : PartBO4Stmt) :
    KFactAGL81I54U4 :=
  kFactAGL81I54U4_of_inputs hC hBO hBO4 torusStepN torusStepO

theorem kFactAGL81I54U4_of_ffNatural (hC : U4FFNatural) : KFactAGL81I54U4 :=
  kFactAGL81I54U4_of_partBO hC partBO_stmt partBO4_stmt

end CFSG.LocalAnalysis.RankThreeUC
