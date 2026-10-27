module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.B69K

open Equiv Equiv.Perm

lemma digits_sum_two_mul_eq (k : ℕ) : (Nat.digits 2 (2 * k)).sum = (Nat.digits 2 k).sum := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * k),
      show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega, List.sum_cons, zero_add]

lemma odd_of_mul_two_pow_mul_factorial_eq {k N : ℕ}
    (h : N * (2 ^ k * Nat.factorial k) = Nat.factorial (2 * k)) : Odd N := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact Nat.factorial_ne_zero _ h.symm
  have hpos : 2 ^ k * Nat.factorial k ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ two_ne_zero) (Nat.factorial_ne_zero k)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul (p := 2) hN0 hpos,
    padicValNat.mul (p := 2) (pow_ne_zero _ two_ne_zero) (Nat.factorial_ne_zero k),
    padicValNat.prime_pow (p := 2)] at hv
  have L1 := sub_one_mul_padicValNat_factorial (p := 2) (2 * k)
  have L2 := sub_one_mul_padicValNat_factorial (p := 2) k
  rw [show (2 : ℕ) - 1 = 1 by norm_num, one_mul] at L1
  rw [show (2 : ℕ) - 1 = 1 by norm_num, one_mul] at L2
  have hdig := digits_sum_two_mul_eq k
  have hle := Nat.digit_sum_le 2 k
  have hv0 : padicValNat 2 N = 0 := by omega
  have hnd : ¬ 2 ∣ N := by
    rcases padicValNat.eq_zero_iff.mp hv0 with h1 | h1 | h1
    · norm_num at h1
    · exact absurd h1 hN0
    · exact h1
  exact Nat.odd_iff.mpr (by omega)

lemma fpf_involution_iff_cycleType {k : ℕ} (σ : Perm (Fin (2 * k))) :
    σ.cycleType = Multiset.replicate k 2 ↔ σ * σ = 1 ∧ ∀ x, σ x ≠ x := by
  constructor
  · intro h
    have hsum : σ.cycleType.sum = 2 * k := by
      rw [h]
      simp [Multiset.sum_replicate, mul_comm]
    have hsupp : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [← Equiv.Perm.sum_cycleType, hsum, Fintype.card_fin]
    refine ⟨?_, fun x => ?_⟩
    · have hord : orderOf σ ∣ 2 := by
        rw [← Equiv.Perm.lcm_cycleType]
        apply Multiset.lcm_dvd.mpr
        intro b hb
        rw [h] at hb
        exact dvd_of_eq (Multiset.eq_of_mem_replicate hb)
      rw [← sq]
      exact orderOf_dvd_iff_pow_eq_one.mp hord
    · have hx : x ∈ σ.support := by
        rw [hsupp]
        exact Finset.mem_univ x
      exact Equiv.Perm.mem_support.mp hx
  · rintro ⟨hinv, hfix⟩
    have hsupp : σ.support = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun x => Equiv.Perm.mem_support.mpr (hfix x)
    have hsum : σ.cycleType.sum = 2 * k := by
      rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ, Fintype.card_fin]
    have hsq : σ ^ 2 = 1 := by
      rw [sq]
      exact hinv
    have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hall : ∀ n ∈ σ.cycleType, n = 2 := by
      intro n hn
      have h1 : n ∣ orderOf σ := by
        rw [← Equiv.Perm.lcm_cycleType]
        exact Multiset.dvd_lcm hn
      have h2 : n ≤ 2 := Nat.le_of_dvd (by norm_num) (h1.trans hord)
      have h3 := Equiv.Perm.two_le_of_mem_cycleType hn
      omega
    have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
      Multiset.eq_replicate_card.mpr hall
    have hsum' := congrArg Multiset.sum hrep
    simp only [Multiset.sum_replicate, smul_eq_mul] at hsum'
    have hc : Multiset.card σ.cycleType = k := by omega
    rw [hc] at hrep
    exact hrep

lemma card_fpf_involution_odd {k : ℕ} (hk : 1 ≤ k) :
    Odd ({g | g.cycleType = Multiset.replicate k 2} : Finset (Perm (Fin (2 * k)))).card := by
  apply odd_of_mul_two_pow_mul_factorial_eq
  have hsum : (Multiset.replicate k 2).sum = k * 2 := by
    simp [Multiset.sum_replicate]
  have hprod : (Multiset.replicate k 2).prod = 2 ^ k := by
    simp [Multiset.prod_replicate]
  have hif : (Multiset.replicate k 2).sum ≤ Fintype.card (Fin (2 * k)) ∧
      ∀ a ∈ Multiset.replicate k 2, 2 ≤ a := by
    refine ⟨?_, fun a ha => le_of_eq (Multiset.eq_of_mem_replicate ha).symm⟩
    rw [hsum, Fintype.card_fin]
    omega
  have key := Equiv.Perm.card_of_cycleType_mul_eq (Fin (2 * k)) (Multiset.replicate k 2)
  rw [if_pos hif, Fintype.card_fin, hsum, hprod, Multiset.toFinset_replicate,
    if_neg (show ¬ k = 0 by omega), Finset.prod_singleton, Multiset.count_replicate_self,
    show 2 * k - k * 2 = 0 by omega, Nat.factorial_zero, one_mul] at key
  exact key

lemma exists_conj_fixed_of_odd {n : ℕ} (G : Subgroup (Perm (Fin n))) (hG : IsPGroup 2 G)
    (S : Finset (Perm (Fin n))) (hS : ∀ g ∈ G, ∀ σ ∈ S, g * σ * g⁻¹ ∈ S)
    (hodd : Odd S.card) : ∃ σ ∈ S, ∀ g ∈ G, g * σ * g⁻¹ = σ := by
  letI act : MulAction G S :=
    { smul := fun g s => ⟨(g : Perm (Fin n)) * s.1 * (g : Perm (Fin n))⁻¹, hS _ g.2 s.1 s.2⟩
      one_smul := fun s => Subtype.ext (by
        change ((1 : G) : Perm (Fin n)) * s.1 * ((1 : G) : Perm (Fin n))⁻¹ = s.1
        simp)
      mul_smul := fun g h s => Subtype.ext (by
        change ((g * h : G) : Perm (Fin n)) * s.1 * ((g * h : G) : Perm (Fin n))⁻¹ =
          (g : Perm (Fin n)) * ((h : Perm (Fin n)) * s.1 * (h : Perm (Fin n))⁻¹) *
            (g : Perm (Fin n))⁻¹
        simp [mul_assoc]) }
  have hnd : ¬ 2 ∣ Nat.card (↥S) := by
    rw [Nat.card_eq_finsetCard]
    obtain ⟨j, hj⟩ := hodd
    omega
  obtain ⟨x, hx⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hG (↥S) hnd
  refine ⟨x.1, x.2, fun g hg => ?_⟩
  have h := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hx ⟨g, hg⟩)
  exact h

theorem exists_fpf_involution_comm {m : ℕ} (hev : Even m) (hm : 2 ≤ m)
    (T' : Subgroup (Perm (Fin m))) (hT' : IsPGroup 2 T') :
    ∃ ι : Perm (Fin m), ι * ι = 1 ∧ (∀ x, ι x ≠ x) ∧ ∀ τ ∈ T', τ * ι = ι * τ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := by
    obtain ⟨r, hr⟩ := hev
    exact ⟨r, by omega⟩
  have hk : 1 ≤ k := by omega
  have hS : ∀ g ∈ T', ∀ σ ∈ ({g | g.cycleType = Multiset.replicate k 2} :
      Finset (Perm (Fin (2 * k)))), g * σ * g⁻¹ ∈ ({g | g.cycleType = Multiset.replicate k 2} :
      Finset (Perm (Fin (2 * k)))) := by
    intro g _ σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.cycleType_conj]
    exact hσ
  obtain ⟨σ, hσS, hfix⟩ := exists_conj_fixed_of_odd T' hT'
    ({g | g.cycleType = Multiset.replicate k 2} : Finset (Perm (Fin (2 * k)))) hS
    (card_fpf_involution_odd hk)
  have hσ := (fpf_involution_iff_cycleType σ).mp (Finset.mem_filter.mp hσS).2
  refine ⟨σ, hσ.1, hσ.2, fun τ hτ => ?_⟩
  have h2 := congrArg (· * τ) (hfix τ hτ)
  simpa [mul_assoc] using h2

end CFSG.Quasithin.B69K
