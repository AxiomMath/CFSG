module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

@[expose] def HeldKDiagonalComponentStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L →
    ∀ (a u : X) (M : Subgroup X), orderOf a = 2 → L ≤ centralizer ({a} : Set X) →
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) → HeldTwoA L u →
      M ≤ centralizer ({u} : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))) → conjugate M a ≠ M →
      gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u →
      (∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) →
      ∀ w : X, orderOf w = 2 → M ≤ centralizer ({w} : Set X) →
        IsPComponent 2 (M.subgroupOf (centralizer ({w} : Set X)))

@[expose] def HeldKDiagonalComponentRestStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L →
    ∀ (a u : X) (M : Subgroup X), orderOf a = 2 → L ≤ centralizer ({a} : Set X) →
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) → HeldTwoA L u →
      M ≤ centralizer ({u} : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))) → conjugate M a ≠ M →
      gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u →
      (∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) →
      ∀ w : X, orderOf w = 2 → M ≤ centralizer ({w} : Set X) →
        (w ∈ M → ∀ N : Subgroup X, N ≤ centralizer ({w} : Set X) →
          IsPComponent 2 (N.subgroupOf (centralizer ({w} : Set X))) → conjugate N u = N →
          M ≤ N → (pPrimeCore 2 ↥N).index ≤ (pPrimeCore 2 ↥M).index) →
        IsPComponent 2 (M.subgroupOf (centralizer ({w} : Set X)))

end CFSG.ComponentClassification.GrSLit
