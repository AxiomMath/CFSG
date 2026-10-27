module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts

public section

namespace CFSG.EvenSporadicStandard.Induction

theorem sol78Hyp35StepAmb_of_rowFacts {A Up Lo S : List TauCeti.SporadicName}
    {Q : TauCeti.SporadicName → PairClass} (row : Stage3Row S Q) (lit : Sol78Lit)
    (lx : Hyp.Hyp31LitX) (rf : Hyp.Hyp31RowFacts row.IsK S Up Lo)
    (hsub : ∀ s ∈ S ++ Up ++ Lo, s ∈ A) : Sol78Hyp35StepAmb A Up S Q :=
  sol78Hyp35StepAmb_of_stage3 row lit
    ((Hyp.hyp31OfBelow_of_rowFacts rf lx).mono_ambient hsub)
    (fun H _ _ => lemma33_two row.IsK (IsLS S) H)

theorem sol78Hyp35StepAmb_withGlobals_of_rowFacts {A Up Lo S : List TauCeti.SporadicName}
    {Q : TauCeti.SporadicName → PairClass} (row : Stage3Row S Q) (lit : Sol78Lit)
    (lx : Hyp.Hyp31LitX) (rf : Hyp.Hyp31RowFacts row.IsK S Up Lo)
    (hsub : ∀ s ∈ S ++ Up ++ Lo, s ∈ A) (htwo : TwoSylowStd S) (htmem : TMemOfNotMax S Q) :
    Sol78Hyp35StepAmb A Up S (fun s => (Q s).withGlobals) :=
  sol78Hyp35StepAmb_withGlobals row lit
    ((Hyp.hyp31OfBelow_of_rowFacts rf lx).mono_ambient hsub)
    (fun H _ _ => lemma33_two row.IsK (IsLS S) H) htwo htmem

@[expose] def rowEntry (S Up : List TauCeti.SporadicName) (Q : TauCeti.SporadicName → PairClass) :
    DepRow :=
  ⟨⟨S, Q⟩, Up⟩

theorem rowEntry_ok {A Up Lo S : List TauCeti.SporadicName}
    {Q : TauCeti.SporadicName → PairClass} (row : Stage3Row S Q) (lit : Sol78Lit)
    (lx : Hyp.Hyp31LitX) (rf : Hyp.Hyp31RowFacts row.IsK S Up Lo)
    (hsub : ∀ s ∈ S ++ Up ++ Lo, s ∈ A) (hclose : Sol78Closing S Q) :
    Sol78Hyp35StepAmb A (rowEntry S Up Q).up (rowEntry S Up Q).row.types
        (rowEntry S Up Q).row.pairs ∧
      Sol78ClosingHered (rowEntry S Up Q).row.types (rowEntry S Up Q).row.pairs :=
  ⟨sol78Hyp35StepAmb_of_rowFacts row lit lx rf hsub, hclose.hered⟩

theorem rowEntry_ok_withGlobalsHered {A Up Lo S : List TauCeti.SporadicName}
    {Q : TauCeti.SporadicName → PairClass} (row : Stage3Row S Q) (lit : Sol78Lit)
    (lx : Hyp.Hyp31LitX) (rf : Hyp.Hyp31RowFacts row.IsK S Up Lo)
    (hsub : ∀ s ∈ S ++ Up ++ Lo, s ∈ A) (htwo : TwoSylowStd S) (htmem : TMemOfNotMax S Q)
    (hclose : Sol78ClosingHered S (fun s => (Q s).withGlobals)) :
    Sol78Hyp35StepAmb A (rowEntry S Up (fun s => (Q s).withGlobals)).up
        (rowEntry S Up (fun s => (Q s).withGlobals)).row.types
        (rowEntry S Up (fun s => (Q s).withGlobals)).row.pairs ∧
      Sol78ClosingHered (rowEntry S Up (fun s => (Q s).withGlobals)).row.types
        (rowEntry S Up (fun s => (Q s).withGlobals)).row.pairs :=
  ⟨sol78Hyp35StepAmb_withGlobals_of_rowFacts row lit lx rf hsub htwo htmem, hclose⟩

theorem rowEntry_ok_withGlobals {A Up Lo S : List TauCeti.SporadicName}
    {Q : TauCeti.SporadicName → PairClass} (row : Stage3Row S Q) (lit : Sol78Lit)
    (lx : Hyp.Hyp31LitX) (rf : Hyp.Hyp31RowFacts row.IsK S Up Lo)
    (hsub : ∀ s ∈ S ++ Up ++ Lo, s ∈ A) (htwo : TwoSylowStd S) (htmem : TMemOfNotMax S Q)
    (hclose : Sol78Closing S (fun s => (Q s).withGlobals)) :
    Sol78Hyp35StepAmb A (rowEntry S Up (fun s => (Q s).withGlobals)).up
        (rowEntry S Up (fun s => (Q s).withGlobals)).row.types
        (rowEntry S Up (fun s => (Q s).withGlobals)).row.pairs ∧
      Sol78ClosingHered (rowEntry S Up (fun s => (Q s).withGlobals)).row.types
        (rowEntry S Up (fun s => (Q s).withGlobals)).row.pairs :=
  rowEntry_ok_withGlobalsHered row lit lx rf hsub htwo htmem hclose.hered

@[expose] def sevenRows (QON QSuz QM QB QCo1 QHN QRu : TauCeti.SporadicName → PairClass) :
    List DepRow :=
  [rowEntry [.ONan] [] QON, rowEntry [.Suz] [.ONan] QSuz, rowEntry [.M] [] QM,
    rowEntry [.B] [.M] QB, rowEntry [.Co1] [] QCo1, rowEntry [.HN] [] QHN,
    rowEntry [.Ru] [] QRu]

theorem depOrdered_sevenRows
    (QON QSuz QM QB QCo1 QHN QRu : TauCeti.SporadicName → PairClass) :
    DepOrdered [] (sevenRows QON QSuz QM QB QCo1 QHN QRu) := by
  simp [sevenRows, rowEntry, DepOrdered]

theorem sol78PredS_sevenRows
    (QON QSuz QM QB QCo1 QHN QRu : TauCeti.SporadicName → PairClass) {A : List TauCeti.SporadicName}
    (hA : ∀ s ∈ A, s = .ONan ∨ s = .Suz ∨ s = .M ∨ s = .B ∨ s = .Co1 ∨ s = .HN ∨ s = .Ru)
    (hrows : ∀ r ∈ sevenRows QON QSuz QM QB QCo1 QHN QRu,
      Sol78Hyp35StepAmb A r.up r.row.types r.row.pairs ∧
        Sol78ClosingHered r.row.types r.row.pairs)
    (H : Type) [Group H] [Finite H] (hH : Balance.UHered H) : Sol78PredS A H := by
  refine sol78PredS_of_depRows (depOrdered_sevenRows QON QSuz QM QB QCo1 QHN QRu) ?_ hrows H hH
  intro s hs
  rcases hA s hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sevenRows, rowEntry]

end CFSG.EvenSporadicStandard.Induction
