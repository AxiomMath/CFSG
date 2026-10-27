module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PerfectCentralizerBlock
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CenterCore

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.UnitaryLevi CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryScalar Matrix Polynomial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] in
theorem exists_perfect_centralizer_of_fixed_space (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (x : StatedSU n (2 ^ f) K) (hx : ((x : GL (Fin n) K)) ^ 3 = 1)
    (hfix : 4 ≤ Module.finrank K (LinearMap.ker (Matrix.mulVecLin
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)))) :
    ∃ W : Subgroup (StatedSU n (2 ^ f) K), W ≠ ⊥ ∧ ⁅W, W⁆ = W ∧ ∀ w ∈ W, Commute w x := by
  classical
  have hM : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
      Matrix.scalar (Fin n) (1 : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hx
    simpa using this
  have hsq := squarefree_minpoly_of_pow_scalar Nat.prime_three (by norm_num) _ one_ne_zero hM
  set y : Module.End K (Fin n → K) :=
    mulVecLin ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hy
  have hker : LinearMap.ker (Matrix.mulVecLin
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)) =
      primaryComponent y (X - C (1 : K)) := by
    rw [primaryComponent_X_sub_C_one]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp [hy]
  rw [hker] at hfix
  have hpos : 0 < Module.finrank K (primaryComponent y (X - C (1 : K))) := by omega
  have ha : (X - C (1 : K) : K[X]) ∈ primaryFactors y := by
    obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    refine X_sub_C_mem_primaryFactors (μ := 1) ?_
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (v : Fin n → K)) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact mem_primaryComponent_X_sub_C.mp v.2
    · exact fun h0 => hv (Subtype.ext h0)
  have hm : 4 ≤ primaryMultiplicity y (X - C (1 : K)) := by
    rw [primaryMultiplicity_X_sub_C_one]
    exact hfix
  refine exists_perfect_centralizer_of_good_block hK hf x hsq ha
    (show 2 ≤ primaryMultiplicity y (X - C (1 : K)) by omega) fun _ hmem => ?_
  rw [← hy] at hmem
  generalize primaryMultiplicity y (X - C (1 : K)) = m at hm hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  omega

end CFSG.HardMathSupport.Curtis.UnitaryLevi
