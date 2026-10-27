module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TCaseA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TCaseII
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TCaseIIIp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82KStatements

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup CFSG.ComponentClassification.GSThmB.Eight2

theorem gs82CaseA10EpsZeroInput_of_inputs
    (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    (hA8 : EvenPump.A8PumpInput) (hHNfix : HNFixedComponents)
    (hHNinner : HNInnerFixedComponents) (hHNidx : HNOuterIndex) (hR18 : GS82R18Input) :
    GS82CaseA10EpsZeroInput := by
  intro X _ _ s hN hA _hε
  obtain ⟨c, -⟩ := exists_ctx hN hA
  obtain ⟨d⟩ := c.nonempty_propBData
  rcases d.cases with ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact d.false_of_case_i h1 h2
  · exact d.false_of_case_ii hcore hHN hHNfix h1
  · exact d.false_of_case_iii h1 h2
  · exact d.false_of_case_iii' hcore hHN hA8 hHNfix hHNinner hHNidx hR18 h1 h2

theorem gs82CentXA10TransferStatementK_of_inputs
    (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    (hA8 : EvenPump.A8PumpInput) (hHNfix : HNFixedComponents)
    (hHNinner : HNInnerFixedComponents) (hHNidx : HNOuterIndex) (hR18 : GS82R18Input) :
    GS82CentXA10TransferStatementK :=
  fun X _ _ s hN hA hε _ _ _ _ _ =>
    (gs82CaseA10EpsZeroInput_of_inputs hcore hHN hA8 hHNfix hHNinner hHNidx hR18 X s hN hA
      hε).elim

end CFSG.ComponentClassification.GSThmB.A10T
