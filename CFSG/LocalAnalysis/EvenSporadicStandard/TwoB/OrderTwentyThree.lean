module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.EvenSporadicStandard.TwoB

open MulAction

theorem no_order_23_isometry {K : Type} [CommRing K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] [Finite V]
    (hV : Nat.card V = 2 ^ 12) (q : QuadraticForm K V)
    (hq : ∀ u, (∀ v, QuadraticMap.polar q u v = 0) → u = 0)
    (g : V ≃ₗ[K] V) (hg : orderOf g = 23) (hiso : ∀ v, q (g v) = q v) : False := by
  classical
  have h23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hg23 : g ^ 23 = 1 := hg ▸ pow_orderOf_eq_one g
  have hpol : ∀ x y, QuadraticMap.polar q (g x) (g y) = QuadraticMap.polar q x y := by
    intro x y
    simp only [QuadraticMap.polar]
    rw [← map_add, hiso, hiso, hiso]
  have hpol_pow : ∀ (i : ℕ) x y,
      QuadraticMap.polar q ((g ^ i) x) ((g ^ i) y) = QuadraticMap.polar q x y := by
    intro i
    induction i with
    | zero => intro x y; simp
    | succ i ih =>
      intro x y
      rw [pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih, hpol]
  have hself : ∀ x, QuadraticMap.polar q x x = 0 := by
    intro x
    have hxx : x + x = 0 := by
      rw [← two_smul K x]
      have : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      rw [this, zero_smul]
    have h2 := CharTwo.add_self_eq_zero (q x)
    have h3 : q (x + x) = 0 := by rw [hxx]; exact QuadraticMap.map_zero q
    simp only [QuadraticMap.polar]
    rw [h3, sub_sub, h2, sub_self]
  let f : V →ₗ[K] V := (g : V →ₗ[K] V) - LinearMap.id
  let F : AddSubgroup V := (LinearMap.ker f).toAddSubgroup
  have hF : ∀ v, v ∈ F ↔ g v = v := by
    intro v
    show f v = 0 ↔ g v = v
    simp [f, sub_eq_zero]
  have hFpow : ∀ v ∈ F, ∀ i : ℕ, (g ^ i) v = v := by
    intro v hv i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, LinearEquiv.mul_apply, (hF v).1 hv, ih]
  have hH : IsPGroup 23 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hfixiff : ∀ v, v ∈ fixedPoints (Subgroup.zpowers g) V ↔ v ∈ F := by
    intro v
    rw [mem_fixedPoints]
    constructor
    · intro h
      exact (hF v).2 (h ⟨g, Subgroup.mem_zpowers g⟩)
    · intro hv m
      obtain ⟨m, hm⟩ := m
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
      show (g ^ k) v = v
      rw [← zpow_mod_orderOf, hg]
      have hk : (0 : ℤ) ≤ k % ((23 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hk
      rw [hn, zpow_natCast]
      exact hFpow v hv n
  have hmod := IsPGroup.card_modEq_card_fixedPoints hH V
  have hcardfix : Nat.card (fixedPoints (Subgroup.zpowers g) V) = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquivRight hfixiff)
  rw [hV, hcardfix] at hmod
  have hdvd : Nat.card F ∣ 2 ^ 12 := hV ▸ AddSubgroup.card_addSubgroup_dvd_card F
  obtain ⟨f', hf, hFeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hFeq] at hmod
  have hf' : f' = 1 ∨ f' = 12 := by
    interval_cases f' <;>
      first | (left; rfl) | (right; rfl) | (exfalso; revert hmod; norm_num [Nat.ModEq])
  rcases hf' with rfl | rfl
  · have hc2 : Nat.card F = 2 := by rw [hFeq]; norm_num
    obtain ⟨v, hv0, huniq⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hc2
    have hvF : (v : V) ∈ F := v.2
    have hvne : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
    have hFcases : ∀ u ∈ F, u = 0 ∨ u = (v : V) := by
      intro u hu
      by_cases h0 : u = 0
      · exact Or.inl h0
      · right
        have := huniq ⟨u, hu⟩ (fun h => h0 (congrArg Subtype.val h))
        exact congrArg Subtype.val this
    have hperp : ∀ y, QuadraticMap.polar q (v : V) y = 0 := by
      intro y
      set y' : V := ∑ i ∈ Finset.range 23, (g ^ i) y with hy'
      have hgy' : g y' = y' := by
        have h1 : g y' = ∑ i ∈ Finset.range 23, (g ^ (i + 1)) y := by
          rw [hy', map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pow_succ' g i, LinearEquiv.mul_apply]
        have h2 := Finset.sum_range_succ' (fun i => (g ^ i) y) 23
        have h3 := Finset.sum_range_succ (fun i => (g ^ i) y) 23
        rw [h1]
        have h4 : (g ^ 23) y = (g ^ 0) y := by rw [hg23]; simp
        have h5 : ∑ i ∈ Finset.range 23, (g ^ (i + 1)) y + (g ^ 0) y =
            ∑ i ∈ Finset.range 23, (g ^ i) y + (g ^ 23) y := h2.symm.trans h3
        rw [h4] at h5
        exact add_right_cancel h5
      have hsum : QuadraticMap.polar q (v : V) y' = QuadraticMap.polar q (v : V) y := by
        have h1 : QuadraticMap.polar q (v : V) y' =
            ∑ i ∈ Finset.range 23, QuadraticMap.polar q (v : V) ((g ^ i) y) := by
          have := map_sum ((QuadraticMap.polarBilin q : V →ₗ[K] V →ₗ[K] K)
            (v : V)) (fun i => (g ^ i) y) (Finset.range 23)
          simp only [QuadraticMap.polarBilin_apply_apply] at this
          exact this
        have h2 : ∀ i ∈ Finset.range 23, QuadraticMap.polar q (v : V) ((g ^ i) y) =
            QuadraticMap.polar q (v : V) y := by
          intro i _
          have := hpol_pow i (v : V) y
          rwa [hFpow _ hvF i] at this
        rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range]
        generalize QuadraticMap.polar q (v : V) y = r
        have h22 : (22 : ℕ) • r = 0 := by
          rw [show (22 : ℕ) = 2 * 11 by norm_num, mul_nsmul, two_nsmul,
            CharTwo.add_self_eq_zero r, nsmul_zero]
        rw [show (23 : ℕ) = 22 + 1 by norm_num, add_nsmul, h22, zero_add, one_nsmul]
      rcases hFcases y' ((hF y').2 hgy') with h0 | h0
      · rw [← hsum, h0]
        exact QuadraticMap.polar_zero_right q _
      · rw [← hsum, h0]
        exact hself _
    exact hvne (hq _ hperp)
  · have hc : Nat.card F = Nat.card V := by rw [hFeq, hV]
    have htop : F = ⊤ := AddSubgroup.eq_top_of_card_eq F hc
    have hg1 : g = 1 := LinearEquiv.ext fun v => (hF v).1 (htop ▸ AddSubgroup.mem_top v)
    rw [hg1, orderOf_one] at hg
    omega

end CFSG.EvenSporadicStandard.TwoB
