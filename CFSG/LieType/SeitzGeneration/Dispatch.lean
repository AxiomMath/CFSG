module

public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def IsClassicalIndex : TauCeti.LieTypeIndex → Prop
  | .A _ _ => True
  | .twistedA _ _ => True
  | .B _ _ => True
  | .C _ _ => True
  | .D _ _ => True
  | .twistedD _ _ => True
  | _ => False

@[expose] def SeitzInnerClassicalFive : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ IsClassicalIndex d.1

@[expose] def SeitzInnerExceptionalFive : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ ¬ IsClassicalIndex d.1

@[expose] def SeitzInnerThree : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3

theorem kFactSeitzRankTwoInner_of_pieces (h₁ : SeitzInnerClassicalFive)
    (h₂ : SeitzInnerExceptionalFive) (h₃ : SeitzInnerThree) : KFactSeitzRankTwoInner :=
  have h5 : SeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p :=
    SeitzPlanes.of_cover (fun d _ _ _ E hE => by
      by_cases hc : IsClassicalIndex d.1
      exacts [Or.inl ⟨hE.1, hE.2, hc⟩, Or.inr ⟨hE.1, hE.2, hc⟩]) h₁ h₂
  SeitzPlanes.of_cover (fun _ p hp hp2 E hE => by
    have h2 := hp.two_le
    rcases (by omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h
    · exact Or.inl ⟨hE, h⟩
    · subst h
      exact absurd hp (by norm_num)
    · exact Or.inr ⟨hE, h⟩) h₃ h5

theorem kFactSeitzRankTwo_of_pieces (h₁ : SeitzInnerClassicalFive)
    (h₂ : SeitzInnerExceptionalFive) (h₃ : SeitzInnerThree) (h₄ : KFactSeitzRankTwoOuter) :
    KFactSeitzRankTwo :=
  kFactSeitzRankTwo_of_inner_outer (kFactSeitzRankTwoInner_of_pieces h₁ h₂ h₃) h₄

end CFSG.LieType.SeitzGeneration
