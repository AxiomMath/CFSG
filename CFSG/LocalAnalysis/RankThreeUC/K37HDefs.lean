module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Rest

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover)

variable {X : Type} [Group X] [Finite X]

@[expose] def K37Open₁ (K E : Subgroup X) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
    ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧
      (q.card = 2 ∨ ¬ autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range)

@[expose] def K37Open₂Two (K : Subgroup X) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
    ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧ q.card = 2

@[expose] def K37Open₂U38 (K E : Subgroup X) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
    ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧ m = 2 ∧ q.card = 8 ∧
      ¬ autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range

@[expose] def K37Open₃ (K : Subgroup X) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .twistedA 3 q) ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def K37Open₄ (K : Subgroup X) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 4 q) ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def K37Open₅ (K : Subgroup X) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
    ∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 3 q

@[expose] def K37Open₆ (K : Subgroup X) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
    ∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .B 3 q

@[expose] def K37Open₇ (K : Subgroup X) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
    ∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .G2 q

@[expose] def K37Open₈ (K : Subgroup X) : Prop :=
  IsThreeCenterCover ↥K (alternatingGroup (Fin 6))

@[expose] def K37Open₉ (K : Subgroup X) : Prop :=
  IsThreeCenterCover ↥K (alternatingGroup (Fin 7))

@[expose] def K37Open₁₀ (K : Subgroup X) : Prop :=
  IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .M22).Group

@[expose] def K37Open₁₁ (K : Subgroup X) : Prop :=
  IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .J3).Group

@[expose] def K37Open₁₂ (K : Subgroup X) : Prop :=
  IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .McL).Group

@[expose] def K37Open₁₃ (K : Subgroup X) : Prop :=
  IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .Suz).Group

@[expose] def K37Open₁₄ (K : Subgroup X) : Prop :=
  IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic .ONan).Group

@[expose] def K37Open₁₅ (K : Subgroup X) : Prop :=
  ∃ s : TauCeti.SporadicName, s ∉ CFSG.RankThree.PartOne.Census3.sporadicsThm3 ∧
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group)

theorem k37Open₂_cases {K E : Subgroup X}
    (h : ∃ d : TauCeti.ValidLieTypeIndex, IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group ∧
      ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧
        (q.card = 2 ∨ (m = 2 ∧ q.card = 8 ∧
          ¬ autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range))) :
    K37Open₂Two K ∨ K37Open₂U38 K E := by
  obtain ⟨d, hc, m, q, hd, h2 | ⟨hm, h8, hE⟩⟩ := h
  · exact Or.inl ⟨d, hc, m, q, hd, h2⟩
  · exact Or.inr ⟨d, hc, m, q, hd, hm, h8, hE⟩

@[expose] def K37RestOf (F : ∀ {X : Type} [Group X] [Finite X], Subgroup X → Subgroup X → Prop) :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E S : Subgroup X), K37Setting X K E S → F K E →
    S ≤ Subgroup.centralizer (K : Set X)

@[expose] def K37Rest₁ : Prop := K37RestOf fun K E => K37Open₁ K E
@[expose] def K37Rest₂Two : Prop := K37RestOf fun K _ => K37Open₂Two K
@[expose] def K37Rest₂U38 : Prop := K37RestOf fun K E => K37Open₂U38 K E
@[expose] def K37Rest₃ : Prop := K37RestOf fun K _ => K37Open₃ K
@[expose] def K37Rest₄ : Prop := K37RestOf fun K _ => K37Open₄ K
@[expose] def K37Rest₅ : Prop := K37RestOf fun K _ => K37Open₅ K
@[expose] def K37Rest₆ : Prop := K37RestOf fun K _ => K37Open₆ K
@[expose] def K37Rest₇ : Prop := K37RestOf fun K _ => K37Open₇ K
@[expose] def K37Rest₈ : Prop := K37RestOf fun K _ => K37Open₈ K
@[expose] def K37Rest₉ : Prop := K37RestOf fun K _ => K37Open₉ K
@[expose] def K37Rest₁₀ : Prop := K37RestOf fun K _ => K37Open₁₀ K
@[expose] def K37Rest₁₁ : Prop := K37RestOf fun K _ => K37Open₁₁ K
@[expose] def K37Rest₁₂ : Prop := K37RestOf fun K _ => K37Open₁₂ K
@[expose] def K37Rest₁₃ : Prop := K37RestOf fun K _ => K37Open₁₃ K
@[expose] def K37Rest₁₄ : Prop := K37RestOf fun K _ => K37Open₁₄ K
@[expose] def K37Rest₁₅ : Prop := K37RestOf fun K _ => K37Open₁₅ K

theorem k37Rest_of_families (h1 : K37Rest₁) (h2 : K37Rest₂Two) (h2' : K37Rest₂U38) (h3 : K37Rest₃)
    (h4 : K37Rest₄) (h5 : K37Rest₅) (h6 : K37Rest₆) (h7 : K37Rest₇) (h8 : K37Rest₈) (h9 : K37Rest₉)
    (h10 : K37Rest₁₀) (h11 : K37Rest₁₁) (h12 : K37Rest₁₂) (h13 : K37Rest₁₃) (h14 : K37Rest₁₄)
    (h15 : K37Rest₁₅) : K37Rest := by
  intro X _ _ K E S hs hO
  rcases hO with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact h1 X K E S hs h
  · rcases k37Open₂_cases h with h | h
    · exact h2 X K E S hs h
    · exact h2' X K E S hs h
  · exact h3 X K E S hs h
  · exact h4 X K E S hs h
  · exact h5 X K E S hs h
  · exact h6 X K E S hs h
  · exact h7 X K E S hs h
  · exact h8 X K E S hs h
  · exact h9 X K E S hs h
  · exact h10 X K E S hs h
  · exact h11 X K E S hs h
  · exact h12 X K E S hs h
  · exact h13 X K E S hs h
  · exact h14 X K E S hs h
  · exact h15 X K E S hs h

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
