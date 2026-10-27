module

public import CFSG.LargeExtraspecial.AS35WMain
public import CFSG.LargeExtraspecial.AS35WOneLie
public import CFSG.LargeExtraspecial.AS35WOneSpor
public import CFSG.LargeExtraspecial.AS35WAlt
public import CFSG.LargeExtraspecial.S8CBFSmall

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Blueprint

namespace AS35W

@[expose] def Sp4W2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    LieModel X .PSp 2 p f → W2Good X

@[expose] def L4W2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    (p ^ f % 8 = 3 ∨ p ^ f % 8 = 7) → LieModel X .PSL 4 p f → W2Good X

@[expose] def U4W2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    (p ^ f % 8 = 1 ∨ p ^ f % 8 = 5) → LieModel X .PSU 4 p f → W2Good X

@[expose] def L5W2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
    LieModel X .PSL 5 p f → W2Good X

@[expose] def U5W2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → 1 ≤ f → p ^ f % 4 = 1 →
    LieModel X .PSU 5 p f → W2Good X

@[expose] def M12W2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X], NativeSporadic.IsSporadic X .M12 → W2Good X

@[expose] def J2W2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X], NativeSporadic.IsSporadic X .J2 → W2Good X

theorem odd_pow_mod_eight {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ f % 8 = 1 ∨ p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 ∨ p ^ f % 8 = 7 := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨k, hk⟩ := hodd
  omega

theorem gh74W2Input_of
    (hSp4 : Sp4W2Input) (hL4 : L4W2Input) (hU4 : U4W2Input) (hL5 : L5W2Input)
    (hU5 : U5W2Input) (hA8 : W2Good (alternatingGroup (Fin 8))) (hM12 : M12W2Input)
    (hJ2 : J2W2Input) : GH74W2Input := by
  intro X _ _ hr hlist
  rcases hlist with ⟨p, f, hp, hp2, -, h | h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
    ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hf, hq, h⟩ |
    ⟨p, f, hp, hf, hq, h⟩ | h | ⟨n, h8, h11, ⟨e⟩⟩ | h
  · exact w2Good_of_oneClass (oneClass_G2 hp hp2 h) hr
  · exact w2Good_of_oneClass (oneClass_D4 hp hp2 h) hr
  · exact hSp4 X p f hp hp2 hf h
  · exact w2Good_of_oneClass (oneClass_Ree h) hr
  · rcases odd_pow_mod_eight (f := f) hp hp2 with h1 | h1 | h1 | h1
    · exact absurd h1 hq
    · exact hL4 X p f hp hp2 hf (Or.inl h1) h
    · exact w2Good_of_oneClass (oneClass_L4U4 hp hp2 (Or.inl ⟨h1, h⟩)) hr
    · exact hL4 X p f hp hp2 hf (Or.inr h1) h
  · rcases odd_pow_mod_eight (f := f) hp hp2 with h1 | h1 | h1 | h1
    · exact hU4 X p f hp hp2 hf (Or.inl h1) h
    · exact w2Good_of_oneClass (oneClass_L4U4 hp hp2 (Or.inr ⟨h1, h⟩)) hr
    · exact hU4 X p f hp hp2 hf (Or.inr h1) h
    · exact absurd h1 hq
  · exact hL5 X p f hp hf hq h
  · exact hU5 X p f hp hf hq h
  · rcases h with h | h | h | h
    · exact w2Good_of_oneClass (oneClass_of_fusionIsBenderGroup
        (S8.fusionIsBenderGroup_of_lieModel_psl_two h)) hr
    · exact w2Good_of_oneClass (oneClass_of_fusionIsBenderGroup
        (S8.fusionIsBenderGroup_of_lieModel_psl_two h)) hr
    · exact w2Good_of_oneClass (oneClass_L34 h) hr
    · exact w2Good_of_oneClass (oneClass_of_fusionIsBenderGroup
        (S8.fusionIsBenderGroup_of_lieModel_twistedB2 h)) hr
  · rcases Nat.lt_or_ge n 9 with hn | hn
    · obtain rfl : n = 8 := by omega
      exact W2Good.of_mulEquiv e hA8
    · exact W2Good.of_mulEquiv e (w2Good_alternating hn h11)
  · rcases h with h | h | h | h | h | h | h | h
    · exact hM12 X h
    · exact w2Good_of_oneClass (oneClass_M22 h) hr
    · exact w2Good_of_oneClass (oneClass_M23 h) hr
    · exact w2Good_of_oneClass (oneClass_J1 h) hr
    · exact hJ2 X h
    · exact w2Good_of_oneClass (oneClass_J3 h) hr
    · exact w2Good_of_oneClass (oneClass_McL h) hr
    · exact w2Good_of_oneClass (oneClass_Ly h) hr

end AS35W

end CFSG.LargeExtraspecial
