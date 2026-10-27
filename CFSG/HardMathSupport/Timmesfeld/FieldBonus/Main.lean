module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Classify
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSUFour
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.OmegaRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.Assembly.LowTwoRank CFSG.Models

@[expose] def ExceptionalRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n p f : ℕ), LieModel X t n p f →
    t ≠ .PSL → t ≠ .PSU → t ≠ .PSp → t ≠ .POmegaOdd → t ≠ .POmegaPlus → t ≠ .POmegaMinus →
      CFSG.Open.pRank 3 (⊤ : Subgroup X) ≠ 1

theorem unitaryRankTwoOpen_holds :
    ∀ (X : Type) [Group X] [Finite X] (n p f : ℕ), StatedClassicalModel X .PSU n p f → 4 ≤ n →
      p ≠ 3 → p ^ f % 3 = 1 → CFSG.Open.pRank 3 (⊤ : Subgroup X) ≠ 1 := by
  intro X _ _ n p f hC hn hp3 _
  have := two_le_pRank_three_psu_four hn hp3 hC
  omega

theorem orthogonalRankTwoOpen_holds :
    ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n p f : ℕ),
      StatedClassicalModel X t n p f →
        (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → p ≠ 2 → p ≠ 3 →
          CFSG.Open.pRank 3 (⊤ : Subgroup X) ≠ 1 := by
  intro X _ _ t n p f hC ht hp2 hp3
  have := Orth.two_le_pRank_three_orth hC ht hp2 hp3
  omega

theorem lieRankOneOpen_of
    (hE : ExceptionalRankTwo) : LieRankOneOpen := by
  have hU := unitaryRankTwoOpen_holds
  have hO := orthogonalRankTwoOpen_holds
  intro X _ _ t n p f hm hopen
  rcases hopen with ⟨rfl, hn, hp3, hq⟩ | ⟨rfl, hp3⟩ | ⟨hpm, hp2, hp3⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact hU X n p f (statedClassicalModel_of_lieModel (Or.inr (Or.inl rfl)) hm) hn hp3 hq
  · exact hO X _ n p f (statedClassicalModel_of_lieModel
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hm) (Or.inl rfl)
      (fun h => by
        have := (statedClassicalModel_of_lieModel
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hm).1.2.2
        simp at this
        exact this.2 h) hp3
  · rcases hpm with rfl | rfl
    · exact hO X _ n p f (statedClassicalModel_of_lieModel
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hm) (Or.inr (Or.inl rfl)) hp2 hp3
    · exact hO X _ n p f (statedClassicalModel_of_lieModel
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hm) (Or.inr (Or.inr rfl)) hp2 hp3
  · exact hE X t n p f hm h1 h2 h3 h4 h5 h6

theorem tfaaModels_holds_of (hE : ExceptionalRankTwo) :
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.TFAaModels :=
  tfaaModels_of_open (lieRankOneOpen_of hE)

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
