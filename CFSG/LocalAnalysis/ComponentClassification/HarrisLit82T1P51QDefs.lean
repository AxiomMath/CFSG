module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def FamQuat (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (n p f : ℕ), p.Prime → p ≠ 2 →
    Blueprint.LieModel X t n p f → p ^ f ≠ 3 → ∀ z : X, orderOf z = 2 →
    ∀ Q : Subgroup X, Q ≤ centralizer ({z} : Set X) → z ∈ Q →
      (∃ u ∈ Q, ∃ v ∈ Q, u * v ≠ v * u) → (∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z) →
      Nat.card Q = 8 →
      (∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
        ∀ k ∈ K, ∀ g ∈ Q, (k : X) * g = g * k) → False

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
