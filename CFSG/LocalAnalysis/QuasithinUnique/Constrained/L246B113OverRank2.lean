module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def SQTKRank2Native (S : Type) [Group S] : Prop :=
  (∃ f : ℕ, (2 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f)) ∨
  ReeTitsModel S .Tits 2 1 ∨ StatedClassicalModel S .PSL 5 2 1

@[expose] def AsLieRank2FStar : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → SQTKRank2Native S → Overgroups S

structure AsLieRank2Families : Prop where
  l3 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), IsSimpleGroup S → 2 ≤ f →
    StatedClassicalModel S .PSL 3 2 f → Overgroups S
  sp4 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), IsSimpleGroup S → 2 ≤ f →
    StatedClassicalModel S .PSp 2 2 f → Overgroups S
  g2 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), IsSimpleGroup S → 2 ≤ f →
    ChevalleyExceptionalModel S .G2 2 f → Overgroups S
  d4 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), IsSimpleGroup S → 1 ≤ f →
    ChevalleyExceptionalModel S .trialityD4 2 f → Overgroups S
  f4 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), IsSimpleGroup S → Odd f → 3 ≤ f →
    ReeTitsModel S .twistedF4 2 f → Overgroups S
  tits : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ReeTitsModel S .Tits 2 1 →
    Overgroups S
  l5 : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → StatedClassicalModel S .PSL 5 2 1 →
    Overgroups S

theorem AsLieRank2Families.asLieRank2FStar (h : AsLieRank2Families) : AsLieRank2FStar := by
  intro S _ _ hS hN
  rcases hN with ⟨f, hf | hf | hf | hf | hf⟩ | hf | hf
  · exact h.l3 S f hS hf.1 hf.2
  · exact h.sp4 S f hS hf.1 hf.2
  · exact h.g2 S f hS hf.1 hf.2
  · exact h.d4 S f hS hf.1 hf.2
  · exact h.f4 S f hS hf.1 hf.2.1 hf.2.2
  · exact h.tits S hS hf
  · exact h.l5 S hS hf

end CFSG.QuasithinUnique.Bridge.Over
