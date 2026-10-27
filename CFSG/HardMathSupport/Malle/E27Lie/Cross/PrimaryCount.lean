module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

namespace CFSG.HardMathSupport.Malle.E27Lie

universe u

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open scoped Classical in
theorem exists_primaryMultiplicity_gt {x : Module.End K V} (hx : Squarefree (minpoly K x))
    (hdeg : (minpoly K x).natDegree ≤ 3) {M : ℕ} (hM : 3 * M < Module.finrank K V) :
    ∃ a : primaryFactors x, M < primaryMultiplicity x (a : K[X]) := by
  by_contra hcon
  push Not at hcon
  have hsum := finrank_eq_sum_degree_mul_multiplicity hx
  have h1 : Module.finrank K V ≤ ∑ a : primaryFactors x, (a : K[X]).natDegree * M := by
    refine hsum.le.trans (Finset.sum_le_sum fun a _ => ?_)
    exact Nat.mul_le_mul_left _ (hcon a)
  have hprod := prod_primaryFactors hx
  have hne : ∀ a ∈ primaryFactors x, a ≠ 0 := fun a ha =>
    (UniqueFactorizationMonoid.irreducible_of_normalized_factor a
      (Multiset.mem_toFinset.1 ha)).ne_zero
  have hdeg' : (minpoly K x).natDegree = ∑ a ∈ primaryFactors x, a.natDegree := by
    rw [← hprod, Polynomial.natDegree_prod _ _ hne]
  have h2 : ∑ a : primaryFactors x, (a : K[X]).natDegree = ∑ a ∈ primaryFactors x, a.natDegree :=
    Finset.sum_coe_sort (primaryFactors x) fun a => a.natDegree
  rw [← Finset.sum_mul, h2, ← hdeg'] at h1
  nlinarith

end CFSG.HardMathSupport.Malle.E27Lie
