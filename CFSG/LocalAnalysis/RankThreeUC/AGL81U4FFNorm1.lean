module

public import Mathlib.Algebra.Lie.OfAssociative
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.LocalAnalysis.RankThreeUC

private theorem natDegree_minpoly_eq_two_mul {E : Type*} [Field E] [Finite E]
    [Algebra (ZMod 2) E] {n : ℕ} (hn : 1 ≤ n) (hE : Nat.card E = (2 ^ n) ^ 2) {ω : E}
    (hω : ω ^ (2 ^ n + 1) = 1) (hord : orderOf ω = 2 ^ n + 1) :
    (minpoly (ZMod 2) ω).natDegree = 2 * n := by
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hω0 : ω ≠ 0 := by
    rintro rfl
    have h0 : 2 ^ n + 1 ≠ 0 := by omega
    rw [zero_pow h0] at hω
    exact zero_ne_one hω
  have hω_int : IsIntegral (ZMod 2) ω := Algebra.IsIntegral.isIntegral ω
  set d := (minpoly (ZMod 2) ω).natDegree with hd_def
  have hd_pos : 0 < d := minpoly.natDegree_pos hω_int
  set K : IntermediateField (ZMod 2) E := IntermediateField.adjoin (ZMod 2) ({ω} : Set E) with hK
  have hdeg : Module.finrank (ZMod 2) K = d := IntermediateField.adjoin.finrank hω_int
  have hKcard : Nat.card K = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥K), Nat.card_zmod, hdeg]
  have hEfin : Module.finrank (ZMod 2) E = 2 * n := by
    have h1 : Nat.card E = 2 ^ Module.finrank (ZMod 2) E := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), Nat.card_zmod]
    have h2 : 2 ^ Module.finrank (ZMod 2) E = 2 ^ (2 * n) := by
      rw [← h1, hE, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective (le_refl 2) h2
  have htower : Module.finrank (ZMod 2) K * Module.finrank K E = Module.finrank (ZMod 2) E :=
    Module.finrank_mul_finrank (ZMod 2) K E
  have hdvd : d ∣ 2 * n := by
    rw [← hEfin, ← htower, hdeg]
    exact dvd_mul_right d _
  have hωK : ω ∈ K := IntermediateField.subset_adjoin (ZMod 2) ({ω} : Set E) (Set.mem_singleton ω)
  have hpowK : ω ^ (2 ^ d - 1) = 1 := by
    haveI : Fintype K := Fintype.ofFinite K
    have hne : (⟨ω, hωK⟩ : K) ≠ 0 := by
      intro h
      exact hω0 (by simpa using congrArg Subtype.val h)
    have h := FiniteField.pow_card_sub_one_eq_one _ hne
    rw [← Nat.card_eq_fintype_card, hKcard] at h
    simpa using congrArg Subtype.val h
  have hdiv : 2 ^ n + 1 ∣ 2 ^ d - 1 := by
    have := orderOf_dvd_of_pow_eq_one hpowK
    rwa [hord] at this
  have h2d : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd_pos
  have hle : 2 ^ n + 1 ≤ 2 ^ d - 1 := Nat.le_of_dvd (by omega) hdiv
  have hd_le : d ≤ 2 * n := Nat.le_of_dvd (by omega) hdvd
  by_contra hne
  have hlt : d < 2 * n := lt_of_le_of_ne hd_le hne
  obtain ⟨t, ht⟩ := hdvd
  have hdn : d ≤ n := by
    rcases Nat.lt_or_ge t 2 with ht2 | ht2
    · interval_cases t
      · omega
      · omega
    · have : d * 2 ≤ d * t := Nat.mul_le_mul (le_refl d) ht2
      omega
  have hpow_le : 2 ^ d ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hdn
  omega

theorem exists_primitive_normOne {E : Type*} [Field E] [Finite E] [Algebra (ZMod 2) E] {n : ℕ}
    (hn : 1 ≤ n) (hE : Nat.card E = (2 ^ n) ^ 2) :
    ∃ ω : E, ω ^ (2 ^ n + 1) = 1 ∧ ω ≠ 1 ∧ (minpoly (ZMod 2) ω).natDegree = 2 * n := by
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard : Nat.card Eˣ = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [Nat.card_units, hE]
    obtain ⟨r, hr⟩ : ∃ r, 2 ^ n = r + 1 := ⟨2 ^ n - 1, by omega⟩
    have h1 : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
    rw [hr, Nat.add_sub_cancel, h1, Nat.add_sub_cancel]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hord : orderOf g = (2 ^ n - 1) * (2 ^ n + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hpos : 0 < 2 ^ n - 1 := by omega
  have hdvd : 2 ^ n - 1 ∣ orderOf g := ⟨2 ^ n + 1, hord⟩
  obtain ⟨u, hu⟩ : ∃ u : Eˣ, u = g ^ (2 ^ n - 1) := ⟨_, rfl⟩
  have huord : orderOf u = 2 ^ n + 1 := by
    rw [hu, orderOf_pow_of_dvd (by omega) hdvd, hord, Nat.mul_div_cancel_left _ hpos]
  have hu_pow : u ^ (2 ^ n + 1) = 1 := by
    rw [← huord]
    exact pow_orderOf_eq_one u
  have hω_pow : (u : E) ^ (2 ^ n + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu_pow, Units.val_one]
  have hω_ord : orderOf (u : E) = 2 ^ n + 1 := by
    rw [orderOf_units, huord]
  refine ⟨(u : E), hω_pow, ?_, natDegree_minpoly_eq_two_mul hn hE hω_pow hω_ord⟩
  intro h
  have h1 : u = 1 := Units.val_eq_one.mp h
  rw [h1, orderOf_one] at huord
  omega

end CFSG.LocalAnalysis.RankThreeUC
