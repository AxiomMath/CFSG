module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowEntries
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONRowInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzAutFixOfN0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONRowAtlas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONOuterPerfect
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Parts
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONStage3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzRowAtlas
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzRowAtlas
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONRowAtlas

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Sporadic.SuzOddCore

theorem suz_entry_row
    {A : List TauCeti.SporadicName} (lit : Sol78Lit) (lx : Hyp31LitX) (hfix : SuzFixedNotLam)
    (inp : SuzRowInputs) (hSuz : TauCeti.SporadicName.Suz ∈ A)
    (hON : TauCeti.SporadicName.ONan ∈ A) :
    EntryOK A (rowEntry [.Suz] [.ONan] (fun _ => SuzQ)) :=
  rowEntry_ok (stage3Row_suz_proved (suzAutFix_of_autCentralizerN0 inp.aut_centralizer) hfix
      lit.lemma25) lit lx (hyp31RowFacts_suz_row lit lieModelOrders inp) (by simp [hSuz, hON])
    sol78Closing_suz

theorem on_entry_row
    {A : List TauCeti.SporadicName} (lit : Sol78Lit) (lx : Hyp31LitX)
    (hmult : OddMultThree .ONan) (inp : ONRowInputs) (hON : TauCeti.SporadicName.ONan ∈ A)
    (hSuz : TauCeti.SporadicName.Suz ∈ A) :
    EntryOK A (rowEntry [.ONan] [] (fun _ => ONQ)) :=
  rowEntry_ok (stage3Row_on_proved inp.k2_fixed) lit lx
    (hyp31RowFacts_on_row lit lieModelOrders inp) (by simp [hON, hSuz])
    (sol78Closing_on hmult (ONOuterFixedPerfect.of_fixedJ1 inp.outer_j1))

end CFSG.EvenSporadicStandard.Induction
