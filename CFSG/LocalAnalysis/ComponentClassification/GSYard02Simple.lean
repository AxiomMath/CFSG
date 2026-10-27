module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Cases

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Blueprint

@[expose] def LeafG2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → 3 ≤ Open.twoRank X →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → LieModel X .G2 0 p f → SylowFourJoined X

@[expose] def LeafD4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → 3 ≤ Open.twoRank X →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → LieModel X .trialityD4 0 p f → SylowFourJoined X

@[expose] def LeafPSp4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → 3 ≤ Open.twoRank X →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → LieModel X .PSp 2 p f → SylowFourJoined X

@[expose] def LeafRee : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → 3 ≤ Open.twoRank X →
    ∀ f : ℕ, LieModel X .twistedG2 0 3 f → SylowFourJoined X

@[expose] def LeafL4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → 3 ≤ Open.twoRank X →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 → LieModel X .PSL 4 p f →
      SylowFourJoined X

@[expose] def LeafU4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → 3 ≤ Open.twoRank X →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 → LieModel X .PSU 4 p f →
      SylowFourJoined X

@[expose] def LeafL5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → 3 ≤ Open.twoRank X →
    ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → LieModel X .PSL 5 p f → SylowFourJoined X

@[expose] def LeafU5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → 3 ≤ Open.twoRank X →
    ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → LieModel X .PSU 5 p f → SylowFourJoined X

@[expose] def LeafSmallEven : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → 3 ≤ Open.twoRank X →
    (LieModel X .PSL 2 2 3 ∨ LieModel X .PSL 2 2 4 ∨ LieModel X .PSL 3 2 2 ∨
      LieModel X .twistedB2 0 2 3) → SylowFourJoined X

@[expose] def LeafAlt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 8 ≤ n → n ≤ 11 →
    Nonempty (X ≃* alternatingGroup (Fin n)) → SylowFourJoined X

@[expose] def LeafSporadic (s : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], 3 ≤ Open.twoRank X → GH74.Gen4 X →
    NativeSporadic.IsSporadic X s → SylowFourJoined X

theorem simpleCase_of_leaves (h1 : LeafG2) (h1' : LeafD4) (h2 : LeafPSp4) (h3 : LeafRee) (h4 : LeafL4)
    (h5 : LeafU4) (h6 : LeafL5) (h7 : LeafU5) (h8 : LeafSmallEven) (h9 : LeafAlt)
    (hM12 : LeafSporadic .M12) (hM22 : LeafSporadic .M22) (hM23 : LeafSporadic .M23)
    (hJ1 : LeafSporadic .J1) (hJ2 : LeafSporadic .J2) (hJ3 : LeafSporadic .J3)
    (hMcL : LeafSporadic .McL) (hLy : LeafSporadic .Ly) : SimpleCase := by
  intro X _ _ hsimp _ hr hgen hc
  rcases hc with ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
      ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hf, hq, h⟩ |
      ⟨p, f, hp, hf, hq, h⟩ | h | ⟨n, hn, hn', h⟩ | h | h | h | h | h | h | h | h
  · rcases h with h | h
    · exact h1 X hsimp hr p f hp hp2 hf h
    · exact h1' X hsimp hr p f hp hp2 hf h
  · exact h2 X hsimp hr p f hp hp2 hf h
  · exact h3 X hsimp hr f h
  · exact h4 X hsimp hr p f hp hp2 hf hq h
  · exact h5 X hsimp hr p f hp hp2 hf hq h
  · exact h6 X hsimp hr p f hp hf hq h
  · exact h7 X hsimp hr p f hp hf hq h
  · exact h8 X hsimp hr h
  · exact h9 X n hn hn' h
  · exact hM12 X hr hgen h
  · exact hM22 X hr hgen h
  · exact hM23 X hr hgen h
  · exact hJ1 X hr hgen h
  · exact hJ2 X hr hgen h
  · exact hJ3 X hr hgen h
  · exact hMcL X hr hgen h
  · exact hLy X hr hgen h

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
