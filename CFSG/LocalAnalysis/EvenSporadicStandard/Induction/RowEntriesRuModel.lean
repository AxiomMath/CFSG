module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowEntries
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuTwoSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRu
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuStage2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuClosing
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzEightStage3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzEightRowFacts

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

theorem ru_entry_model
    {A : List TauCeti.SporadicName} (lit : Sol78Lit) (lx : Hyp31LitX) (hf : RuLocalFacts)
    (hmult : OddMultTrivial .Ru) (hbal : RuBalanceHered) (gh1 : RuStd.S2.GHLemma53_1)
    (inp : RuHyp31Inputs) (hRu : TauCeti.SporadicName.Ru ∈ A) :
    EntryOK A (rowEntry [.Ru] [] (fun _ => (RuPair).withGlobals)) :=
  rowEntry_ok_withGlobalsHered
    (stage3Row_ru' hf inp.suzuki szEightModel_proved hmult
      (ruNoOtherHered_proved hf hmult hbal gh1 RuStd.S2.outU43TwoGroup)
      (twoSylowStd_ru lit.lemma25)) lit lx
    (hyp31RowFacts_ru' hf szEightModel_proved hmult lieModelOrders inp)
    (by simp [hRu]) (twoSylowStd_ru lit.lemma25) (tMemOfNotMax_ru_proved hf hmult)
    (sol78ClosingHered_ru_proved hf hmult hbal)

end CFSG.EvenSporadicStandard.Induction
