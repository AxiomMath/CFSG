module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def Rank2CharTwoNative (S : Type) [Group S] : Prop :=
  (∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f)) ∨
  ReeTitsModel S .Tits 2 1 ∨ StatedClassicalModel S .PSL 5 2 1

@[expose] def SylowAutTrivial (S : Type) [Group S] : Prop :=
  ∀ (P : Sylow 2 S) (α : MulAut S), Odd (orderOf α) → (∀ t ∈ (P : Subgroup S), α t = t) → α = 1

@[expose] def AsLieRank2SylowAut : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Rank2CharTwoNative S → SylowAutTrivial S

structure AsLieRank2SylowAutFamilies : Prop where
  l3 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), 2 ≤ f → StatedClassicalModel S .PSL 3 2 f →
    SylowAutTrivial S
  sp4 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), 2 ≤ f → StatedClassicalModel S .PSp 2 2 f →
    SylowAutTrivial S
  g2 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), 2 ≤ f →
    ChevalleyExceptionalModel S .G2 2 f → SylowAutTrivial S
  d4 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), 1 ≤ f →
    ChevalleyExceptionalModel S .trialityD4 2 f → SylowAutTrivial S
  f4 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), Odd f → 3 ≤ f →
    ReeTitsModel S .twistedF4 2 f → SylowAutTrivial S
  tits : ∀ (S : Type) [Group S] [Finite S], ReeTitsModel S .Tits 2 1 → SylowAutTrivial S
  l5 : ∀ (S : Type) [Group S] [Finite S], StatedClassicalModel S .PSL 5 2 1 → SylowAutTrivial S

theorem AsLieRank2SylowAutFamilies.asLieRank2SylowAut (h : AsLieRank2SylowAutFamilies) :
    AsLieRank2SylowAut := by
  intro S _ _ hS
  rcases hS with ⟨f, hf | hf | hf | hf | hf⟩ | hT | hL5
  · exact h.l3 S f hf.1 hf.2
  · exact h.sp4 S f hf.1 hf.2
  · exact h.g2 S f hf.1 hf.2
  · exact h.d4 S f hf.1 hf.2
  · exact h.f4 S f hf.1 hf.2.1 hf.2.2
  · exact h.tits S hT
  · exact h.l5 S hL5

end CFSG.QuasithinUnique.Bridge
