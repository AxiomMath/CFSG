module

public import CFSG.FeitThompson.OddOrder.NormPointCharacterIdentity
public import CFSG.FeitThompson.Representations.ColumnOrthogonalityCentralizerOrders
public import CFSG.FeitThompson.Foundations.CounterorderedPrimeParity
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open SemidirectProduct
open scoped ComplexConjugate

variable {F : Type*} [Field F] {U : Subgroup Fˣ} {p q m : ℕ}

theorem two_ne_zero_of_natCard_eq_prime_pow (hp : p.Prime) (hodd : Odd p)
    (hFcard : Nat.card F = p ^ q) :
    haveI : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
    (2 : F) ≠ 0 := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
  have : CharP F p := charP_of_natCard_eq_prime_pow hp hFcard
  refine Ring.two_ne_zero ?_
  rw [ringChar.eq F p]
  rintro rfl
  simp [Nat.odd_iff] at hodd

section Orthogonality

variable {G : Type*} [Group G] [Finite G]

theorem sum_irrFinset_normSq_eq_natCard_centralizer (x : G) :
    ∑ χ ∈ irrFinset G, ‖χ x‖ ^ 2 = (Nat.card (Subgroup.centralizer ({x} : Set G)) : ℝ) := by
  have _i : Fintype (Irr G) := (finite_Irr (G := G)).fintype
  rw [← sum_Irr_normSq_eq_natCard_centralizer x,
    ← Finset.sum_coe_sort (irrFinset G) (fun χ => ‖χ x‖ ^ 2)]
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun _ => mem_irrFinset) _ _ (fun _ => rfl)

theorem sq_norm_le_natCard_centralizer {χ : G → ℂ} (hχ : χ ∈ Irr G) (x : G) :
    ‖χ x‖ ^ 2 ≤ (Nat.card (Subgroup.centralizer ({x} : Set G)) : ℝ) := by
  rw [← sum_irrFinset_normSq_eq_natCard_centralizer x]
  exact Finset.single_le_sum (f := fun ψ : G → ℂ => ‖ψ x‖ ^ 2) (fun _ _ => sq_nonneg _)
    (mem_irrFinset.2 hχ)

theorem norm_le_sqrt_natCard_centralizer {χ : G → ℂ} (hχ : χ ∈ Irr G) (x : G) :
    ‖χ x‖ ≤ Real.sqrt (Nat.card (Subgroup.centralizer ({x} : Set G))) :=
  (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).2 (sq_norm_le_natCard_centralizer hχ x)

end Orthogonality

theorem natCard_centralizer_fieldAffinePointOne :
    Nat.card (Subgroup.centralizer ({fieldAffinePointOne F U} : Set (fieldAffineGroup F U)))
      = Nat.card F := by
  rw [fieldAffinePointOne_eq, centralizer_inl_ofAdd_eq_fieldAffineBase (one_ne_zero (α := F)),
    natCard_fieldAffineBase]

theorem natCard_centralizer_fieldAffinePointOne_sq (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.centralizer ({fieldAffinePointOne F U ^ 2} : Set (fieldAffineGroup F U)))
      = Nat.card F := by
  rw [fieldAffinePointOne_sq, centralizer_inl_ofAdd_eq_fieldAffineBase h2, natCard_fieldAffineBase]

theorem abs_natCard_mul_ncard_fieldAffineSquarePairs_sub_sq_le [Finite F] (h2 : (2 : F) ≠ 0) :
    |(Nat.card F : ℝ) * (fieldAffineSquarePairs F U).ncard - (Nat.card U : ℝ) ^ 2|
      ≤ (Nat.card F : ℝ) * Real.sqrt (Nat.card F) := by
  set s : fieldAffineGroup F U := fieldAffinePointOne F U with hs
  set e : ℕ := (fieldAffineSquarePairs F U).ncard with he
  have hcast : ((Nat.card F : ℂ) * (e : ℂ) - (Nat.card U : ℂ) ^ 2)
      = (((Nat.card F : ℝ) * (e : ℝ) - (Nat.card U : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  have hnorm : |(Nat.card F : ℝ) * (e : ℝ) - (Nat.card U : ℝ) ^ 2|
      = ‖(Nat.card F : ℂ) * (e : ℂ) - (Nat.card U : ℂ) ^ 2‖ := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, natCard_mul_ncard_fieldAffineSquarePairs_sub_sq]
  calc ‖∑ χ ∈ fieldAffineDetectFinset F U, χ s ^ 2 * conj (χ (s ^ 2))‖
      ≤ ∑ χ ∈ fieldAffineDetectFinset F U, ‖χ s ^ 2 * conj (χ (s ^ 2))‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ fieldAffineDetectFinset F U, ‖χ s‖ ^ 2 * Real.sqrt (Nat.card F) := by
        refine Finset.sum_le_sum fun χ hχ => ?_
        have hIrr : χ ∈ Irr (fieldAffineGroup F U) := (mem_fieldAffineDetectFinset.1 hχ).1
        have hb : ‖χ (s ^ 2)‖ ≤ Real.sqrt (Nat.card F) := by
          have := norm_le_sqrt_natCard_centralizer hIrr (s ^ 2)
          rwa [hs, natCard_centralizer_fieldAffinePointOne_sq h2] at this
        rw [norm_mul, norm_pow, RCLike.norm_conj]
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (∑ χ ∈ fieldAffineDetectFinset F U, ‖χ s‖ ^ 2) * Real.sqrt (Nat.card F) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ χ ∈ irrFinset (fieldAffineGroup F U), ‖χ s‖ ^ 2) * Real.sqrt (Nat.card F) :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg fieldAffineDetectFinset_subset_irrFinset
            fun _ _ _ => sq_nonneg _) (Real.sqrt_nonneg _)
    _ = (Nat.card F : ℝ) * Real.sqrt (Nat.card F) := by
        rw [sum_irrFinset_normSq_eq_natCard_centralizer, hs,
          natCard_centralizer_fieldAffinePointOne]

section Config

theorem abs_natCard_mul_ncard_normOneShiftSet_sub_sq_le_of_config (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hFcard : Nat.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (hcop : Nat.Coprime m (p - 1)) :
    haveI : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
    |((p ^ q : ℕ) : ℝ) * (normOneShiftSet F m).ncard - (m : ℝ) ^ 2|
      ≤ ((p ^ q : ℕ) : ℝ) * Real.sqrt ((p ^ q : ℕ) : ℝ) := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
  have hodd : Odd p := (odd_of_coprime_pow_sub_one_div_sub_one hp hq hqp (hm ▸ hcop)).2.2.1
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_natCard_eq_prime_pow hp hodd hFcard
  have hm0 : m ≠ 0 := by
    rw [hm, ← Nat.geomSum_eq hp.two_le]
    exact (geomSum_pos_of_natCard_eq_prime_pow (F := F) hp hFcard).ne'
  have hU : Nat.card (normOneSubgroup F m) = m := natCard_normOneSubgroup hp hFcard hm
  have key := abs_natCard_mul_ncard_fieldAffineSquarePairs_sub_sq_le
    (F := F) (U := normOneSubgroup F m) h2
  rwa [ncard_fieldAffineSquarePairs (F := F) hm0, hU, hFcard] at key

end Config

end

end CFSG.FeitThompson
