module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseIOuter

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

@[expose] def CaseICoords.symm {A B R T : Subgroup G} (c : CaseICoords A B R T) :
    CaseICoords B A T R where
  pair := c.pair.symm
  ψA := c.ψB
  ψB := c.ψA
  mapA := c.mapB
  mapB := c.mapA

@[expose] def CaseIDoubleBad : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    standardComponentOddCore G = ⊥ → ∀ (R T : Subgroup G) (g : G)
    (c : CaseICoords A (rightConjugate A g) R T),
    c.w ∈ rightConjugate A g ⊔ c.Bx → c.symm.w ∈ A ⊔ c.symm.Bx → False

end CFSG.ComponentClassification.RankTwoAltFive
