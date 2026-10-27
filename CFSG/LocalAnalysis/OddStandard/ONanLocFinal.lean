module

public import CFSG.LocalAnalysis.OddStandard.ONanLocOne
public import CFSG.LocalAnalysis.OddStandard.ONanLocSyl
public import CFSG.Goldschmidt.Final

public section

namespace CFSG.OddStandard.ONanRec

theorem stageB1Local_of_gold
    (hgold : CFSG.Goldschmidt.CoreStatement) : StageB1Local := by
  intro G _ _ _ hna v1 v2 v3 s t hfr hz hSyl
  obtain ⟨P, hP⟩ := hSyl
  let D := FusCtx.ofStage hna hfr hz P hP
  exact ⟨D.oneClass hna hgold, D.exists_sylow_quot f2QuotCheck_cert⟩

theorem stageB1Local :
    StageB1Local :=
  stageB1Local_of_gold CFSG.Goldschmidt.coreStatement

end CFSG.OddStandard.ONanRec
