module

public import CFSG.CGT.Timmesfeld75.FinalNodeRest
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.L32NSp4Over

public section

namespace CFSG.LargeExtraspecial.TI75Bridge

open CFSG.CGT.Timmesfeld75

theorem simpleCaseStmt_of_rest (I : NodeInputsRest) : SimpleCaseStmt := by
  intro G _ _ _ hna T hT h4
  have hL : ListGroup G := simpleCaseListStmt_final_rest I G hna T hT h4
  exact ⟨hL, (listWCIdentification_of_cert G hL T hT h4).transitive⟩

end CFSG.LargeExtraspecial.TI75Bridge
