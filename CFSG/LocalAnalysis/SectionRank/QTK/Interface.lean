module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.LocalAnalysis.SectionRank.QTK.Basic

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def QTAltRestriction : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n : ℕ), CFSG.Open.evenRank S ≤ 2 →
    Nonempty (S ≃* alternatingGroup (Fin n)) → n ≤ 9

@[expose] def QTOddClassicalRestriction : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (t : StatedLieTag) (n p f : ℕ), p ≠ 2 →
    CFSG.Open.evenRank S ≤ 2 → StatedClassicalModel S t n p f → QTKSimpleList S

@[expose] def QTEvenClassicalRestriction : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (t : StatedLieTag) (n f : ℕ),
    CFSG.Open.evenRank S ≤ 2 → StatedClassicalModel S t n 2 f → QTKSimpleList S

@[expose] def QTExceptionalList (S : Type) [Group S] : Prop :=
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ChevalleyExceptionalModel S .G2 p 1) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
    (∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
    (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨
    ReeTitsModel S .Tits 2 1 ∨
    (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f)

@[expose] def QTExceptionalRestriction : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.Open.evenRank S ≤ 2 → ExceptionalRep S →
    QTExceptionalList S

@[expose] def QTSporadicRestriction : Prop :=
  ∀ (S : Type) [Group S] [Finite S], (∃ a b : S, a * b ≠ b * a) → CFSG.Open.evenRank S ≤ 2 →
    ∀ s : TauCeti.SporadicName, Nonempty (S ≃* NativeSporadic.Carrier s) →
      s ∈ qtkSporadicNames

end CFSG.SectionRank.QTK
