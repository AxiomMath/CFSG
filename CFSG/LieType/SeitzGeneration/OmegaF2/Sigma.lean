module

public import CFSG.LieType.SeitzGeneration.RootPairOrthModel
public import CFSG.LieType.SeitzGeneration.RootPairOrthTail

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.LieType.SeitzGeneration.RootPairOrth

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {k : Subfield K}
  {Q₀ : QuadraticForm k (Fin d → k)}

@[expose] def sigmaVec (σ : K ≃+* K) (v : Fin d → K) : Fin d → K := fun i => σ (v i)

private theorem polar_eq_sum_basis (u v : Fin d → K) :
    polar Q u v = ∑ r, ∑ c, u r * v c * polar Q (Pi.single r 1 : Fin d → K) (Pi.single c 1) := by
  rw [polar_expand_left u v]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [polar_expand_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem polar_sigmaVec (hext : IsExtension k Q₀ Q) {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x)
    (u v : Fin d → K) : polar Q (sigmaVec σ u) (sigmaVec σ v) = σ (polar Q u v) := by
  have hfix : ∀ r c : Fin d,
      σ (polar Q (Pi.single r 1 : Fin d → K) (Pi.single c 1)) =
        polar Q (Pi.single r 1 : Fin d → K) (Pi.single c 1) := fun r c =>
    (hσk _).mp (polar_isRat_mem hext (isRat_single k r) (isRat_single k c))
  rw [polar_eq_sum_basis (sigmaVec σ u) (sigmaVec σ v), polar_eq_sum_basis u v]
  simp only [map_sum, map_mul, sigmaVec, hfix]

theorem sigmaVec_isRat {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x) {v : Fin d → K}
    (hv : IsRat k v) : sigmaVec σ v = v := by
  funext i
  exact (hσk (v i)).mp (hv i)

theorem sigmaVec_add (σ : K ≃+* K) (u v : Fin d → K) :
    sigmaVec σ (u + v) = sigmaVec σ u + sigmaVec σ v := by
  funext i
  simp [sigmaVec]

theorem sigmaVec_smul (σ : K ≃+* K) (c : K) (v : Fin d → K) :
    sigmaVec σ (c • v) = σ c • sigmaVec σ v := by
  funext i
  simp [sigmaVec]

end CFSG.LieType.SeitzGeneration.OmegaF2
