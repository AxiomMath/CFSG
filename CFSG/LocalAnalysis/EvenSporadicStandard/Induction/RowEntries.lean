module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNRowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MBPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Row
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BStage3Proved
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Gen
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Parts
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3HN
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3M
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BStage3Proved
import all CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1RowAtlas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNOdd

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def EntryOK (A : List TauCeti.SporadicName) (r : DepRow) : Prop :=
  Sol78Hyp35StepAmb A r.up r.row.types r.row.pairs ∧ Sol78ClosingHered r.row.types r.row.pairs

theorem hn_entry
    {A : List TauCeti.SporadicName} (lit : Sol78Lit) (lx : Hyp31LitX)
    (hmult : OddMultTrivial .HN) (inp : HNHyp31Inputs) (hHN : TauCeti.SporadicName.HN ∈ A) :
    EntryOK A (rowEntry [.HN] [] (fun _ => HNPair)) :=
  rowEntry_ok (stage3Row_hn hmult) lit lx
    (hyp31RowFacts_hn hmult lieModelOrders inp) (by simp [hHN])
    (sol78Closing_hn hmult hnOddCore)

theorem m_entry
    {A : List TauCeti.SporadicName} (lit : Sol78Lit) (lx : Hyp31LitX) (hfix : MFixesElem)
    (inp : MHyp31Inputs) (hM : TauCeti.SporadicName.M ∈ A) (hB : TauCeti.SporadicName.B ∈ A) :
    EntryOK A (rowEntry [.M] [] (fun _ => MPair)) :=
  rowEntry_ok (stage3Row_m (Hyp.oddMultTrivial_m inp.noCover) hfix) lit lx
    (hyp31RowFacts_m_pinned inp) (by simp [hM, hB])
    (sol78Closing_m (Hyp.oddMultTrivial_m inp.noCover))

theorem b_entry
    {A : List TauCeti.SporadicName} (lit : Sol78Lit) (lx : Hyp31LitX) (hfix : BFixesElem)
    (inp : BHyp31InputsNoPair) (hB : TauCeti.SporadicName.B ∈ A)
    (hM : TauCeti.SporadicName.M ∈ A) :
    EntryOK A (rowEntry [.B] [.M] (fun _ => BPair)) :=
  rowEntry_ok (stage3Row_b_proved inp.cover inp.mult hfix) lit lx
    (hyp31RowFacts_b_pinned lit inp.toInputs) (by simp [hB, hM])
    (sol78Closing_b inp.cover inp.mult babyOddCore)

theorem co1_entry
    {A : List TauCeti.SporadicName} (lit : Sol78Lit) (lx : Hyp31LitX)
    (hmult : OddMultTrivial .Co1) (hpair : Co1PinnedPair) (hsol : Co1AutCentralizerA4)
    (hfix : G24FixedNonsolvable) (htmem : Co1TMemOfNotMax) (inp : Co1Hyp31Inputs)
    (hCo1 : TauCeti.SporadicName.Co1 ∈ A) :
    EntryOK A (rowEntry [.Co1] [] (fun _ => PairClass.withGlobals Co1Pair)) :=
  rowEntry_ok_withGlobals (stage3Row_co1_proved hmult hpair hsol hfix lit.lemma25) lit lx
    (hyp31RowFacts_co1 lit hmult lieModelOrders inp) (by simp [hCo1])
    (twoSylowStd_co1 lit.lemma25 co1_pRank_L) htmem (sol78Closing_co1 hmult)

end CFSG.EvenSporadicStandard.Induction
