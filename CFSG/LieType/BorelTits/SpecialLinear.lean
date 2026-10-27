module

public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.BorelTits.Matrix
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LieType.BorelTits

open Matrix CFSG.Assembly.LowTwoRank

theorem containsTransvections_natRep_statedSL (n : ℕ) (K : Type) [Field K] :
    ContainsTransvections (natRep (StatedSL n K)) := by
  intro x φ hφ
  set y : Fin n → K := fun i => φ (Pi.single i 1)
  have hφy : ∀ v, φ v = y ⬝ᵥ v := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  set A : Matrix (Fin n) (Fin n) K := 1 + vecMulVec x y with hA
  have hdet : A.det = 1 := by
    rw [hA, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, ← hφy, hφ, add_zero]
  let g : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero A (by rw [hdet]; exact one_ne_zero)
  have hg : g ∈ StatedSL n K := Subgroup.subset_closure hdet
  refine ⟨⟨g, hg⟩, fun v => ?_⟩
  rw [natRep_apply]
  change A *ᵥ v = v + φ v • x
  rw [hA, add_mulVec, one_mulVec, vecMulVec_mulVec, hφy, op_smul_eq_smul]

theorem holds_statedSL (n : ℕ) (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : Holds (StatedSL n K) p :=
  holds_of_containsTransvections (natRep _) p (natRep_injective _)
    (containsTransvections_natRep_statedSL n K)

end CFSG.LieType.BorelTits
