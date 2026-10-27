module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PerfectCentralizerBlock
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CenterCore

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.UnitaryLevi CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary Matrix Polynomial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] in
theorem exists_perfect_centralizer_of_cube_scalar (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hn : 4 ≤ n) (x : StatedSU n (2 ^ f) K)
    (hx : ((x : GL (Fin n) K)) ^ 3 ∈ StatedScalars (Fin n) K)
    (_hxs : ((x : GL (Fin n) K)) ∉ StatedScalars (Fin n) K) :
    ∃ W : Subgroup (StatedSU n (2 ^ f) K), W ≠ ⊥ ∧ ⁅W, W⁆ = W ∧ ∀ w ∈ W, Commute w x := by
  classical
  have hf1 : 1 ≤ f := by omega
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf1
  obtain ⟨c, hc, -⟩ := exists_unit_of_pow_mem_scalars hK (by omega) x hx
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hM : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
      Matrix.scalar (Fin n) (c : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
    simpa [GeneralLinearGroup.coe_scalar] using this.symm
  have hsq := squarefree_minpoly_of_pow_scalar Nat.prime_three (by norm_num) _ hc0 hM
  set y : Module.End K (Fin n → K) :=
    mulVecLin ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hy
  have hmin : minpoly K y ∣ X ^ 3 - C (c : K) := by
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, aeval_C, hy, mulVecLin_pow', hM]
    refine LinearMap.ext fun v => ?_
    ext i
    simp [Matrix.scalar_apply, Module.algebraMap_end_apply]
  have hdeg : ∑ a ∈ primaryFactors y, a.natDegree ≤ 3 := by
    rw [← natDegree_prod_of_monic _ _ (fun a ha => monic_of_mem_primaryFactors ha),
      prod_primaryFactors hsq]
    calc (minpoly K y).natDegree ≤ (X ^ 3 - C (c : K)).natDegree :=
          natDegree_le_of_dvd hmin (X_pow_sub_C_ne_zero (by norm_num) _)
      _ = 3 := natDegree_X_pow_sub_C
  have hsum : n = ∑ a ∈ primaryFactors y, a.natDegree * primaryMultiplicity y a := by
    have h1 := finrank_eq_sum_degree_mul_multiplicity hsq
    rw [Module.finrank_fin_fun] at h1
    exact h1.trans <| Finset.sum_coe_sort (primaryFactors y)
      (fun a => a.natDegree * primaryMultiplicity y a)
  obtain ⟨a, ha, hm⟩ : ∃ a ∈ primaryFactors y, 2 ≤ primaryMultiplicity y a := by
    by_contra hcon
    push Not at hcon
    have : n ≤ ∑ a ∈ primaryFactors y, a.natDegree := by
      refine hsum.le.trans (Finset.sum_le_sum fun a ha => ?_)
      have := hcon a ha
      calc a.natDegree * primaryMultiplicity y a ≤ a.natDegree * 1 :=
            Nat.mul_le_mul_left _ (by omega)
        _ = a.natDegree := mul_one _
    omega
  have hirr : Irreducible a := irreducible_of_mem_primaryFactors ha
  have hdegpos : 1 ≤ a.natDegree := hirr.natDegree_pos
  refine exists_perfect_centralizer_of_good_block hK hf1 x hsq ha hm fun _ hmem => ?_
  have hQ : 4 ≤ 2 ^ (f * a.natDegree) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * a.natDegree) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  generalize 2 ^ (f * a.natDegree) = Q at hQ hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  omega

end CFSG.HardMathSupport.Curtis.UnitaryLevi
