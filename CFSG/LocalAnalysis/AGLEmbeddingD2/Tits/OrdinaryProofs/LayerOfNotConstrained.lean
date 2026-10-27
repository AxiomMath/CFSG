module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SolvableConstraint
public import CFSG.LocalAnalysis.RankThreeTheoremC.HasPrimeConstraintBridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC

theorem pPrimeCore_three_quotient_eq_bot (X : Type) [Group X] [Finite X] :
    CFSG.pPrimeCore 3 (X ⧸ primeComplementCore (G := X) 3) = ⊥ :=
  primeComplementCore_quotient_eq_bot (G := X) 3

theorem layer_ne_bot_of_not_hasPrimeConstraint {X : Type} [Group X] [Finite X]
    (h : ¬ HasPrimeConstraint (G := X) 3) :
    CFSG.layer (X ⧸ primeComplementCore (G := X) 3) ≠ ⊥ := by
  intro hlayer
  apply h
  exact ⟨CFSG.pCore 3 (X ⧸ primeComplementCore (G := X) 3), CFSG.pCore_normal,
    CFSG.pCore_isPGroup,
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot
      (X ⧸ primeComplementCore (G := X) 3) 3 (pPrimeCore_three_quotient_eq_bot X) hlayer⟩

theorem layer_ne_bot_of_not_isPConstrained {X : Type} [Group X] [Finite X]
    (h : ¬ CFSG.ABGLocalTools.IsPConstrained 3 X) :
    CFSG.layer (X ⧸ primeComplementCore (G := X) 3) ≠ ⊥ :=
  layer_ne_bot_of_not_hasPrimeConstraint fun hc =>
    h ((isPConstrained_iff_hasPrimeConstraint (p := 3) (H := X)).2 hc)

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
