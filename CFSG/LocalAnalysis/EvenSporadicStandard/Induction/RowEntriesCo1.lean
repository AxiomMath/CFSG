module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowEntries
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemCo1

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

theorem co1_entry_of_tmem
    {A : List TauCeti.SporadicName} (lit : Sol78Lit) (lx : Hyp31LitX)
    (hmult : OddMultTrivial .Co1) (hpair : Co1PinnedPair) (hsol : Co1AutCentralizerA4)
    (hfix : G24FixedNonsolvable) (inp : Co1Hyp31Inputs) (hCo1 : TauCeti.SporadicName.Co1 ∈ A) :
    EntryOK A (rowEntry [.Co1] [] (fun _ => PairClass.withGlobals Co1Pair)) :=
  co1_entry lit lx hmult hpair hsol hfix (tMemOfNotMax_co1_proved hmult) inp hCo1

end CFSG.EvenSporadicStandard.Induction
