module

public import CFSG.ClassicalInvolution.RouteD.ExoticShapes

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem shapePiece_of_not_admissible {a : ℕ} {t : StatedLieTag} {n : ℕ} (ht : t ≠ .trialityD4)
    (h : ¬ StatedLieAdmissible t n p f) : ShapePiece p f a t n := by
  intro G _ _ _ _ K z S hshape
  exact absurd (admissible_of_localShapeT hshape ht).2 h

@[expose] def ShapeSingleOddLarge (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .POmegaOdd ∧ 4 ≤ n

@[expose] def ShapeSingleOddSmall (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .POmegaOdd ∧ n = 3

@[expose] def ShapeSinglePlusLarge (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .POmegaPlus ∧ 5 ≤ n ∧ n ≠ 6

@[expose] def ShapeSinglePlusSmall (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .POmegaPlus ∧ n = 4

@[expose] def ShapeSingleMinusLarge (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .POmegaMinus ∧ 5 ≤ n

@[expose] def ShapeSingleMinusSmall (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .POmegaMinus ∧ n = 4

theorem rowSingleOrth_of_parts (hOddL : RowPiece p f ShapeSingleOddLarge)
    (hOddS : RowPiece p f ShapeSingleOddSmall) (hPlusL : RowPiece p f ShapeSinglePlusLarge)
    (hPlusS : RowPiece p f ShapeSinglePlusSmall) (hMinusL : RowPiece p f ShapeSingleMinusLarge)
    (hMinusS : RowPiece p f ShapeSingleMinusSmall) : RowPiece p f ShapeSingleOrth := by
  intro a t n h
  obtain ⟨ha, ht | ht | ⟨ht, hn6⟩⟩ := h
  · subst ht
    by_cases h4 : 4 ≤ n
    · exact hOddL a _ n ⟨ha, rfl, h4⟩
    · by_cases h3 : 3 ≤ n
      · exact hOddS a _ n ⟨ha, rfl, by omega⟩
      · exact shapePiece_of_not_admissible (by decide) fun hadm => h3 hadm.2.2.1
  · subst ht
    by_cases h5 : 5 ≤ n
    · exact hMinusL a _ n ⟨ha, rfl, h5⟩
    · by_cases h4 : 4 ≤ n
      · exact hMinusS a _ n ⟨ha, rfl, by omega⟩
      · exact shapePiece_of_not_admissible (by decide) fun hadm => h4 hadm.2.2
  · subst ht
    by_cases h5 : 5 ≤ n
    · exact hPlusL a _ n ⟨ha, rfl, h5, hn6⟩
    · by_cases h4 : 4 ≤ n
      · exact hPlusS a _ n ⟨ha, rfl, by omega⟩
      · exact shapePiece_of_not_admissible (by decide) fun hadm => h4 hadm.2.2

@[expose] def ShapeSingleF4 (a : ℕ) (t : StatedLieTag) (_n : ℕ) : Prop := a = 1 ∧ t = .F4

@[expose] def ShapeSingleE6 (a : ℕ) (t : StatedLieTag) (_n : ℕ) : Prop := a = 1 ∧ t = .E6

@[expose] def ShapeSingleE8 (a : ℕ) (t : StatedLieTag) (_n : ℕ) : Prop := a = 1 ∧ t = .E8

@[expose] def ShapeSingleTwistedE6 (a : ℕ) (t : StatedLieTag) (_n : ℕ) : Prop :=
  a = 1 ∧ t = .twistedE6

theorem rowSingleExc_of_parts (hF4 : RowPiece p f ShapeSingleF4) (hE6 : RowPiece p f ShapeSingleE6)
    (hE8 : RowPiece p f ShapeSingleE8) (hT : RowPiece p f ShapeSingleTwistedE6) :
    RowPiece p f ShapeSingleExc := by
  intro a t n h
  obtain ⟨ha, ht | ht | ht | ht⟩ := h
  · exact hF4 a t n ⟨ha, ht⟩
  · exact hE6 a t n ⟨ha, ht⟩
  · exact hE8 a t n ⟨ha, ht⟩
  · exact hT a t n ⟨ha, ht⟩

end CFSG.ClassicalInvolution.RouteD.Exotic
