module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne

@[expose] def OrthFixedLeDerived (c : StatedLieTag) (n ℓ e p : ℕ) : Prop :=
  StatedLieAdmissible c n ℓ e → p.Prime → 3 < p → p ≠ ℓ →
  match c with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
        subfieldFixedGroup k (coordinateQuadOdd n k) (coordinateQuadOdd n K) ≤
          subfieldDerivedImage k (coordinateQuadOdd_isExtension k n)
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
        subfieldFixedGroup k (coordinateQuadPlus n k) (coordinateQuadPlus n K) ≤
          subfieldDerivedImage k (coordinateQuadPlus_isExtension k n)
  | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (k : Subfield K),
      Nat.card k = ℓ ^ e → Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p →
        (∀ x, x ∈ k ↔ σ x = x) → ∀ b c' : k, (∀ s : k, s ^ 2 + b * s + c' ≠ 0) →
          subfieldFixedGroup k (coordinateQuadMinus n k hn b c')
              (coordinateQuadMinus n K hn (b : K) (c' : K)) ≤
            subfieldDerivedImage k (coordinateQuadMinus_isExtension k n hn b c')
  | _ => False

@[expose] def OrthFixedLeDerivedAll : Prop :=
  ∀ n ℓ e p : ℕ, OrthFixedLeDerived .POmegaOdd n ℓ e p ∧ OrthFixedLeDerived .POmegaPlus n ℓ e p ∧
    OrthFixedLeDerived .POmegaMinus n ℓ e p

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
