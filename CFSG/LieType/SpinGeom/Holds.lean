module

public import CFSG.LieType.SpinGeom.Main
public import CFSG.LieType.SpinGeom.Transitive

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.Sp6Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear QuadraticMap
open scoped Matrix

theorem spinGeom_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ (s : ℕ)
        (QC : QuadraticForm K (Fin (2 * s) → K)) (b : Fin (2 * 4) → K),
        b ≠ 0 → coordinateQuadPlus 4 K b = 0 →
        ∀ (W : AddSubgroup ((Fin (2 * 4) → K) × (Fin (2 * s) → K)))
          (A : Subgroup (GL (Fin (2 * 4)) K)),
          A ≤ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype →
          (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b) →
          (∀ t : K, (t • b, (0 : Fin (2 * s) → K)) ∈ W) →
          (∀ w ∈ W, coordinateQuadPlus 4 K w.1 + QC w.2 = 0) →
          (∀ w ∈ W, polar (coordinateQuadPlus 4 K) w.1 b = 0) →
          (∀ M ∈ spinSeven K, Odd (orderOf M) →
            ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b →
            (∀ w ∈ W, (((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1,
              w.2) ∈ W) ∧
            ∀ a ∈ A, (M : GL (Fin (2 * 4)) K) * a * (M : GL (Fin (2 * 4)) K)⁻¹ ∈ A) →
          (∀ a ∈ A, ∀ x : Fin (2 * 4) → K, polar (coordinateQuadPlus 4 K) x b = 0 →
            ((a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x - x, (0 : Fin (2 * s) → K)) ∈ W) →
          (∀ a ∈ A, ∀ w ∈ W, ∃ t : K,
            (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 - w.1 = t • b) →
          (∀ w ∈ W, (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 = w.1) →
            ∃ t : K, w = (t • b, 0)) →
          Nat.card A * Nat.card W = Nat.card K ^ (2 * 4 - 1 + 2 * s) → False :=
  spinGeom_of_transitive fun K _ _ _ b hb hQ => spinSeven_transitive K b hb hQ

end CFSG.LieType.SpinGeom
