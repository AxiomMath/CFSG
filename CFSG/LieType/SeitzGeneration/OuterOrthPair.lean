module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

@[expose] def OrthPairShape {K : Type} [Field K] (k : Subfield K) {d : ℕ}
    (Q₀ : QuadraticForm k (Fin d → k)) (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ g ∈ (linearConjugationHom Q).range,
    (subfieldFixedGroup k Q₀ Q).map g.toMonoidHom ≠ subfieldFixedGroup k Q₀ Q →
      Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
        ((subfieldFixedGroup k Q₀ Q).map g.toMonoidHom : Set (matrixProjectiveDerived Q))) = ⊤

@[expose] def SubfieldPairOmegaOdd : Prop :=
  ∀ (n ℓ e p : ℕ), 3 ≤ n → ℓ.Prime → ℓ ≠ 2 → 1 ≤ e → p.Prime → 3 < p → p ≠ ℓ →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) →
        OrthPairShape k (coordinateQuadOdd n k) (coordinateQuadOdd n K)

@[expose] def SubfieldPairOmegaPlus : Prop :=
  ∀ (n ℓ e p : ℕ), 4 ≤ n → ℓ.Prime → 1 ≤ e → p.Prime → 3 < p → p ≠ ℓ →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) →
        OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K)

@[expose] def SubfieldPairOmegaMinus : Prop :=
  ∀ (n ℓ e p : ℕ) (hn : 4 ≤ n), ℓ.Prime → 1 ≤ e → p.Prime → 3 < p → p ≠ ℓ →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) → ∀ b c : k, (∀ s : k, s ^ 2 + b * s + c ≠ 0) →
        OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
          (coordinateQuadMinus n K (by omega) (b : K) (c : K))

@[expose] def SubfieldPairOmega : Prop :=
  SubfieldPairOmegaOdd ∧ SubfieldPairOmegaPlus ∧ SubfieldPairOmegaMinus

end CFSG.LieType.SeitzGeneration
