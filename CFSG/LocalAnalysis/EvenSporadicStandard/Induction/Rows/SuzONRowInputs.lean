module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzHyp31B
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONHyp31B
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzDBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOrderEight
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONOrderEight
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONOddCenterProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HeRank

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.Solomon78


structure SuzRowInputs : Prop where
  aut_centralizer : SuzAutCentralizerN0
  outer : SuzOuterNoLink
  k2_fixed : SuzK2FixedNotLam2
  even : EvenCoverExclHered .Suz

structure ONRowInputs : Prop where
  outer_j1 : ONOuterFixedJ1
  k2_fixed : ONK2FixedNotLam


theorem suzHyp31Inputs_of_row (inp : SuzRowInputs) : SuzHyp31Inputs :=
  ⟨suzD_lieModel, inp.aut_centralizer, inp.outer, inp.k2_fixed, suz_sporadicOrderEight,
    onOddCenter_of_certificate, heCoverRank_of_certificate, inp.even⟩

theorem onHyp31Inputs_of_row (inp : ONRowInputs) : ONHyp31Inputs :=
  ⟨suzD_lieModel, inp.outer_j1, inp.k2_fixed, on_sporadicOrderEight, onOddCenter_of_certificate,
    heCoverRank_of_certificate⟩

theorem hyp31RowFacts_suz_row (lit : Sol78Lit) (lo : LieModelOrders) (inp : SuzRowInputs) :
    Hyp.Hyp31RowFacts IsKSuz [.Suz] [.ONan] [] :=
  hyp31RowFacts_suz lit lo (suzHyp31Inputs_of_row inp)

theorem hyp31RowFacts_on_row (lit : Sol78Lit) (lo : LieModelOrders) (inp : ONRowInputs) :
    Hyp.Hyp31RowFacts IsKON [.ONan] [] [.Suz] :=
  hyp31RowFacts_on lit lo (onHyp31Inputs_of_row inp)

end CFSG.EvenSporadicStandard.Induction
