module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def DS81Lemma210Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    CFSG.Blueprint.Catalog X → ∀ τ : X, orderOf τ = 2 →
      CFSG.IsCharacteristicP 2 ↥(centralizer ({τ} : Set X)) →
      IsMulCommutative (CFSG.pCore 2 ↥(centralizer ({τ} : Set X))) →
      ¬ Nonempty (↥(centralizer ({τ} : Set X)) ⧸ CFSG.pCore 2 ↥(centralizer ({τ} : Set X)) ≃*
        Carrier .Co2)

end CFSG.EvenSporadicStandard.TwoB
