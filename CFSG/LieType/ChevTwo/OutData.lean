module

public import CFSG.LieType.ChevTwo.OutDataOrth
public import CFSG.LieType.ChevTwo.OutDataClass
public import CFSG.LieType.ChevTwo.OutDataExc

public section

namespace CFSG.LieType.ChevTwo

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open CFSG.AGLEmbedding (IsClassicalTwoOrG2)
open CFSG.HardMathSupport.Cooperstein.StructureLie (OutTwoRank)
open CFSG.Open (StatedClassicalModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)

@[expose] def Chev2OutTwoRank : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevTwo S → OutTwoRank S

private theorem twoNilpotent_outer_of_POmegaPlus {X : Type} [Group X] {n m : ℕ}
    (h : StatedClassicalModel X .POmegaPlus n 2 m) : TwoNilpotent (Outer X) := by
  have hn : 4 ≤ n := h.1.2.2
  rcases Nat.eq_or_lt_of_le hn with rfl | h5
  · exact twoNilpotent_outer_of_POmegaPlus_four h
  · exact twoNilpotent_outer_of_POmegaPlus_ge_five h5 h

theorem outTwoNilp_of_isChevTwoExc
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : IsChevTwoExc S) : OutTwoNilpConcl S :=
  (outOddAbelian_of_isChevTwoExc h).outTwoNilpConcl

theorem outTwoNilp_of_isClassicalTwoOrG2
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : IsClassicalTwoOrG2 S) : OutTwoNilpConcl S :=
  outTwoNilp_of_isClassicalTwoOrG2_of_orth (fun _ _ _ _ hm => twoNilpotent_outer_of_POmegaPlus hm)
    (fun _ _ _ _ hm => twoNilpotent_outer_of_POmegaMinus hm) hs hna h

theorem outTwoRank_of_isChevTwoExc
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : IsChevTwoExc S) : OutTwoRank S :=
  (outOddAbelian_of_isChevTwoExc h).outTwoRank

end CFSG.LieType.ChevTwo
