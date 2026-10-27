module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCoreTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Yardstones.Md0ec50421ce4

@[expose] def l154ExcRee : TauCeti.CFSGIndex → Prop :=
  onLie fun | .reeF4 _ => True | _ => False

theorem l154_excRest_cover (i : TauCeti.CFSGIndex) (h : l154ExcRest i) :
    l154ExcUntw i ∨ l154ExcTwE6 i ∨ l154ExcTriD4 i ∨ l154ExcRee i := by
  cases i with
  | cyclic p hp => exact h.elim
  | alternating n hn => exact h.elim
  | sporadic s => exact h.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | E6 q => exact Or.inl h.1
    | E7 q => exact Or.inl h.1
    | E8 q => exact Or.inl h.1
    | F4 q => exact Or.inl h.1
    | G2 q => exact Or.inl h
    | twistedE6 q => exact Or.inr (Or.inl h.1)
    | trialityD4 q => exact Or.inr (Or.inr (Or.inl h.1))
    | reeF4 m => exact Or.inr (Or.inr (Or.inr trivial))
    | suzuki m => exact h.elim
    | tits => exact h.elim
    | A r q => exact h.elim
    | twistedA r q => exact h.elim
    | B r q => exact h.elim
    | C r q => exact h.elim
    | D r q => exact h.elim
    | twistedD r q => exact h.elim
    | reeG2 m => exact h.elim

section Assembly

theorem l154NIDOn_excRest (hInn : L154LangInnRes) (hRee : L154NIDOn l154ExcRee) :
    L154NIDOn l154ExcRest :=
  l154NIDOn_mono l154_excRest_cover
    (l154NIDOn_or (l154NIDOn_excUntw hInn)
      (l154NIDOn_or (l154NIDOn_excTwE6 hInn) (l154NIDOn_or (l154NIDOn_excTriD4 hInn) hRee)))

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
