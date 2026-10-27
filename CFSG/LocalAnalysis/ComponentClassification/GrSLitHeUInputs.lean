module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

@[expose] def HeldUDiagonalStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldSetting X L →
    (∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥) →
    ∀ (a u : X) (U T M : Subgroup X), orderOf a = 2 → L ≤ centralizer ({a} : Set X) →
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) →
      U ≤ L → IsFourGroup U → u ∈ U → u ≠ 1 → T ≤ L →
      T ≤ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X) →
      IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X))) →
      IsL34Type (↥T ⧸ Open.fusionZStar ↥T) → U ≤ (Open.fusionZStar ↥T).map T.subtype →
      M ≤ centralizer ({u} : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))) → conjugate M a ≠ M →
      gsFixedLayer (M ⊔ conjugate M a) a = T →
      ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x

end CFSG.ComponentClassification.GrSLit
