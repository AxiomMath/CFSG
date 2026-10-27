module

public import CFSG.CGT.Foote82.Setup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCOmegaBridge

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.AGLEmbedding CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

section Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def IsFPrimeModule (L : Subgroup (GLV V)) : Prop :=
  (∃ n : ℕ, 6 ≤ n ∧ IsAltNaturalModule L n) ∨ IsA7FourModule L ∨ IsOmegaPlusModule L 3 ∨
    IsOmegaMinusModule L 2 ∨ IsOmegaMinusModule L 3 ∨ IsA6Z3Module L

theorem IsFPrimeModule.isFModule {L : Subgroup (GLV V)} (h : IsFPrimeModule L) :
    IsFModule L := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨3, le_rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨2, le_rfl, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨3, by norm_num, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end Module

section Block

variable {G : Type} [Group G]

@[expose] def IsFPrimeType (J : Subgroup G) : Prop :=
  (∃ n : ℕ, 6 ≤ n ∧ IsAltNaturalType J n) ∨ IsA7FourType J ∨ IsOmegaPlusType J 3 ∨
    IsOmegaMinusType J 2 ∨ IsOmegaMinusType J 3 ∨ IsA6Z3Type J

end Block

end CFSG.CGT.Foote82
