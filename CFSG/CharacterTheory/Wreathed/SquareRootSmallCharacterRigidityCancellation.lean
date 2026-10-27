module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityIntegralAverage

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

private theorem power_apply_of_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (operator : Module.End ℂ V) (μ : ℂ) (v : V) (hv : operator v = μ • v) (k : ℕ) :
    (operator ^ k) v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [pow_succ', Module.End.mul_apply, hk, map_smul, hv, smul_smul, pow_succ]

theorem eigenspace_power_eq_of_inverse_power {V : Type*} [AddCommGroup V] [Module ℂ V]
    (operator : Module.End ℂ V) (μ : ℂ) (k l : ℕ)
    (hoperator : (operator ^ k) ^ l = operator) (hμ : (μ ^ k) ^ l = μ) :
    (operator ^ k).eigenspace (μ ^ k) = operator.eigenspace μ := by
  apply Submodule.ext
  intro v
  constructor
  · intro hv
    have h := power_apply_of_eigenvector (operator ^ k) (μ ^ k) v
      (Module.End.mem_eigenspace_iff.mp hv) l
    rw [hoperator, hμ] at h
    exact Module.End.mem_eigenspace_iff.mpr h
  · intro hv
    exact Module.End.mem_eigenspace_iff.mpr
      (power_apply_of_eigenvector operator μ v (Module.End.mem_eigenspace_iff.mp hv) k)

theorem twice_period_power_involution {M : Type*} [Monoid M]
    (m : ℕ) (hm : Even m) (x : M) (hx : x ^ (2 * m) = 1) :
    (x ^ (m + 1)) ^ (m + 1) = x := by
  obtain ⟨a, ha⟩ := hm
  have hindex : (m + 1) * (m + 1) = (2 * m) * (a + 1) + 1 := by rw [ha]; ring
  rw [← pow_mul, hindex, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]

theorem primitive_twice_root_odd_exponent {m : ℕ} (hm : 0 < m) {root : ℂ}
    (hroot : IsPrimitiveRoot root (2 * m)) (t : ℕ) (ht : Odd t) :
    (root ^ t) ^ (m + 1) = root ^ (t + m) := by
  rw [← pow_mul, Nat.mul_add, Nat.mul_one, pow_add]
  have htm : root ^ (t * m) = -1 := by
    rw [Nat.mul_comm, pow_mul, primitive_twice_root_half hm hroot, Odd.neg_one_pow ht]
  rw [htm, pow_add, primitive_twice_root_half hm hroot]
  ring

theorem odd_eigenmultiplicity_eq_half_period {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ) (hm : 0 < m)
    (heven : Even m) (hy : y ^ (2 * m) = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * m)) (hconj : IsConj y (y ^ (m + 1)))
    (t : ℕ) (ht : Odd t) :
    cyclicEigenmultiplicity data y root t = cyclicEigenmultiplicity data y root (t + m) := by
  have hoperator : data.representation y ^ (2 * m) = 1 := by rw [← map_pow, hy, map_one]
  have hμ : (root ^ t) ^ (2 * m) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot.pow_eq_one, one_pow]
  have hspaces := eigenspace_power_eq_of_inverse_power (data.representation y) (root ^ t)
    (m + 1) (m + 1) (twice_period_power_involution m heven _ hoperator)
    (twice_period_power_involution m heven _ hμ)
  rw [primitive_twice_root_odd_exponent hm hroot t ht] at hspaces
  have hdim : cyclicEigenmultiplicity data (y ^ (m + 1)) root (t + m) =
      cyclicEigenmultiplicity data y root t := by
    unfold cyclicEigenmultiplicity
    rw [map_pow, hspaces]
  have hz : (y ^ (m + 1)) ^ (2 * m) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hy, one_pow]
  exact hdim.symm.trans (cyclicEigenmultiplicity_eq_of_isConj data (2 * m)
    (by omega) hy hz root hroot hconj (t + m)).symm

theorem actual_root_odd_eigenmultiplicity_cancellation {G : Type} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (data : FiniteComplexRepresentation G) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) (t : ℕ) (ht : Odd t) :
    cyclicEigenmultiplicity data (actualRoot S e) root t =
      cyclicEigenmultiplicity data (actualRoot S e) root (t + 2 ^ n) := by
  apply odd_eigenmultiplicity_eq_half_period data (actualRoot S e) (2 ^ n)
    (pow_pos (by omega) _) (Even.pow_of_ne_zero even_two (by omega)) _ root hroot _ t ht
  · rw [← actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  · exact isConj_iff.mpr ⟨wreathModelHom S e (Original.x2 (2 ^ n)),
      actualRoot_conjugate_half n (by omega) S e⟩

theorem odd_eigenvalue_pair_trace_cancel {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ) (hm : 0 < m)
    (heven : Even m) (hy : y ^ (2 * m) = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * m)) (hconj : IsConj y (y ^ (m + 1)))
    (t h : ℕ) (ht : Odd t) (hh : Odd h) :
    (cyclicEigenmultiplicity data y root t : ℂ) * root ^ (t * h) +
      (cyclicEigenmultiplicity data y root (t + m) : ℂ) * root ^ ((t + m) * h) = 0 := by
  have hpair : root ^ ((t + m) * h) = -root ^ (t * h) := by
    rw [Nat.add_mul, pow_add]
    have hmh : root ^ (m * h) = -1 := by
      rw [pow_mul, primitive_twice_root_half hm hroot, Odd.neg_one_pow hh]
    rw [hmh]
    ring
  rw [hpair, odd_eigenmultiplicity_eq_half_period data y m hm heven hy root hroot hconj t ht]
  ring

theorem actual_root_odd_eigenvalue_pair_trace_cancel {G : Type} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (data : FiniteComplexRepresentation G) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) (t h : ℕ) (ht : Odd t) (hh : Odd h) :
    (cyclicEigenmultiplicity data (actualRoot S e) root t : ℂ) * root ^ (t * h) +
      (cyclicEigenmultiplicity data (actualRoot S e) root (t + 2 ^ n) : ℂ) *
        root ^ ((t + 2 ^ n) * h) = 0 := by
  apply odd_eigenvalue_pair_trace_cancel data (actualRoot S e) (2 ^ n)
    (pow_pos (by omega) _) (Even.pow_of_ne_zero even_two (by omega)) _ root hroot _ t h ht hh
  · rw [← actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  · exact isConj_iff.mpr ⟨wreathModelHom S e (Original.x2 (2 ^ n)),
      actualRoot_conjugate_half n (by omega) S e⟩

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
