module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.OrderSums
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFormula

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem extendedCentralizer_le_of_involution {z : G} (hz2 : z * z = 1) :
    extendedCentralizer z ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
  intro g hg
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hconj : g⁻¹ * z * g = z := by
    rcases hg with h | h
    · exact h
    · rw [h, hzinv]
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hcomm : Commute z g := by
    have : z * g = g * z := by
      calc z * g = g * (g⁻¹ * z * g) := by group
        _ = g * z := by rw [hconj]
    exact this
  exact (hcomm.zpow_left k).eq

theorem global_order_sum (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {z : G} (hz2 : z * z = 1)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers z : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (quotientBasis : FiniteIrreducibleCharacterBasis L)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    [Fintype π.ker] (hker : ¬ 2 ∣ Nat.card π.ker)
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h)
    (hyodd : Nat.Coprime 2 (orderOf (y : G))) {w₀ : L}
    (hz₀ : π (centralizerSelf z) ∈ (Subgroup.center S₀).map S₀.subtype)
    (hw₀ : w₀ ∈ (Subgroup.center S₀).map S₀.subtype)
    (hz₀2 : π (centralizerSelf z) * π (centralizerSelf z) = 1) (hw₀2 : w₀ * w₀ = 1)
    (hz₀1 : π (centralizerSelf z) ≠ 1) (hw₀1 : w₀ ≠ 1) (hzw : w₀ ≠ π (centralizerSelf z))
    (n : ℂ)
    (hN : ∀ g, ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = g).card : ℂ) ≠ 0 →
      g = π (centralizerSelf z) ∨ g = w₀ ∨ g = π (centralizerSelf z) * w₀)
    (hNz : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = π (centralizerSelf z)).card : ℂ) = 1)
    (hNw : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = w₀).card : ℂ) = n)
    (hNzw : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = π (centralizerSelf z) * w₀).card : ℂ) = n)
    {j : ℕ} (hj : j < 5) :
    (Nat.card G : ℂ) * ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character z * (basis.representation χ).character z *
        (basis.representation χ).character (z * (y : G) ^ j) /
          (basis.representation χ).character 1 =
      (Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) : ℂ) *
        Nat.card (Subgroup.centralizer ({z} : Set G)) *
          Nat.card (Subgroup.centralizer ({z} : Set G)) *
        (if j = 0 then 2 * Nat.card L * n ^ 2 /
          (Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) : ℂ) ^ 2 else 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf ((centralizerSelf z : Subgroup.centralizer
      (Subgroup.zpowers z : Set G)) : G) ∣ 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one (by change z ^ 2 = 1; rw [pow_two, hz2])
  have hform := (brauer_principal_order_formula basis ideal 2 principal hprincipal hz2 hz2
    (Subgroup.centralizer (Subgroup.zpowers z : Set G)) (centralizerSelf z) 1 hzord
    (extendedCentralizer_le_of_involution hz2) localBasis localPrincipal hlocalPrincipal).1
    (y ^ j) (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg Subtype.val (centralizerSelf_commute z (y ^ j)).eq
      exact this.symm) (by
      have hord : orderOf (y ^ j) ∣ orderOf (y : G) := by
        rw [← Subgroup.orderOf_coe, Subgroup.coe_pow]
        exact orderOf_pow_dvd (x := (y : G)) j
      exact Nat.Coprime.coprime_dvd_right hord hyodd)
  have hcoe : ((centralizerSelf z * y ^ j : Subgroup.centralizer
      (Subgroup.zpowers z : Set G)) : G) = z * (y : G) ^ j := by
    rw [Subgroup.coe_mul, Subgroup.coe_pow]; rfl
  rw [hcoe] at hform
  rw [hform]
  congr 1
  rw [← local_order_sum localBasis ideal localPrincipal hlocalPrincipal hL quotientBasis π hπ hker
    y hy hz₀ hw₀ hz₀2 hw₀2 hz₀1 hw₀1 hzw n hN hNz hNw hNzw hj]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  unfold classWeight
  rw [Finset.sum_filter]
  ring

theorem global_order_sum_fourier (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {z : G} (hz2 : z * z = 1)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers z : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (quotientBasis : FiniteIrreducibleCharacterBasis L)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    [Fintype π.ker] (hker : ¬ 2 ∣ Nat.card π.ker)
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h)
    (hyodd : Nat.Coprime 2 (orderOf (y : G))) {w₀ : L}
    (hz₀ : π (centralizerSelf z) ∈ (Subgroup.center S₀).map S₀.subtype)
    (hw₀ : w₀ ∈ (Subgroup.center S₀).map S₀.subtype)
    (hz₀2 : π (centralizerSelf z) * π (centralizerSelf z) = 1) (hw₀2 : w₀ * w₀ = 1)
    (hz₀1 : π (centralizerSelf z) ≠ 1) (hw₀1 : w₀ ≠ 1) (hzw : w₀ ≠ π (centralizerSelf z))
    (n : ℂ)
    (hN : ∀ g, ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = g).card : ℂ) ≠ 0 →
      g = π (centralizerSelf z) ∨ g = w₀ ∨ g = π (centralizerSelf z) * w₀)
    (hNz : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = π (centralizerSelf z)).card : ℂ) = 1)
    (hNw : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = w₀).card : ℂ) = n)
    (hNzw : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = π (centralizerSelf z) * w₀).card : ℂ) = n)
    (ζ : ℂ) (i : ℕ) :
    (Nat.card G : ℂ) * ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character z * (basis.representation χ).character z *
        fiveFourier (basis.representation χ).character ζ z (y : G) i /
          (basis.representation χ).character 1 =
      (5 : ℂ)⁻¹ * ((Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) : ℂ) *
        Nat.card (Subgroup.centralizer ({z} : Set G)) *
          Nat.card (Subgroup.centralizer ({z} : Set G)) *
        (2 * Nat.card L * n ^ 2 /
          (Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) : ℂ) ^ 2)) := by
  have hexp : (Nat.card G : ℂ) *
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character z * (basis.representation χ).character z *
          fiveFourier (basis.representation χ).character ζ z (y : G) i /
            (basis.representation χ).character 1 =
      (5 : ℂ)⁻¹ * ∑ j ∈ Finset.range 5, ζ ^ (4 * i * j) * ((Nat.card G : ℂ) *
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character z * (basis.representation χ).character z *
            (basis.representation χ).character (z * (y : G) ^ j) /
              (basis.representation χ).character 1) := by
    simp only [fiveFourier, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp]
  congr 1
  rw [Finset.sum_congr rfl fun j hj => by
    rw [global_order_sum basis ideal principal hprincipal hz2 localBasis localPrincipal
      hlocalPrincipal hL quotientBasis π hπ hker y hy hyodd hz₀ hw₀ hz₀2 hw₀2 hz₀1 hw₀1 hzw n hN
      hNz hNw hNzw (Finset.mem_range.mp hj)]]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj0
    rw [ite_eq_right hj0, mul_zero, mul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by norm_num)) h0

end CFSG.LyonsUnitaryFour
