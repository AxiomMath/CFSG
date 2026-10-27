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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Module

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι]
  [DecidableEq ι]

section Classes

variable (b : Basis ι K V) (μ : ι → K)

def classSpan (lam : K) : Submodule K V :=
  Submodule.span K (Set.range fun i : {i // μ i = lam} => b i)

theorem finrank_classSpan [FiniteDimensional K V] (lam : K) :
    finrank K (classSpan b μ lam) = Nat.card {i // μ i = lam} := by
  classical
  unfold classSpan
  have hli : LinearIndependent K (fun i : {i // μ i = lam} => b i) :=
    b.linearIndependent.comp (fun i : {i // μ i = lam} => (i : ι)) Subtype.val_injective
  have h := finrank_span_eq_card hli
  rw [Nat.card_eq_fintype_card]
  exact h

variable {b μ}

theorem eigen_of_mem_classSpan {a : Module.End K V} (ha : ∀ i, a (b i) = μ i • b i) {lam : K}
    {x : V} (hx : x ∈ classSpan b μ lam) : a x = lam • x := by
  unfold classSpan at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hy
    simp [ha, hi]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, hx, smul_comm]

theorem mem_classSpan_of_eigen {a : Module.End K V} (ha : ∀ i, a (b i) = μ i • b i) {lam : K}
    {y : V} (hy : a y = lam • y) : y ∈ classSpan b μ lam := by
  have hrepr : ∀ i, μ i * b.repr y i = lam * b.repr y i := by
    intro i
    have h1 : a y = ∑ j, (b.repr y j * μ j) • b j := by
      conv_lhs => rw [← b.sum_repr y]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ha, smul_smul]
    have h2 : b.repr (a y) = fun j => b.repr y j * μ j := by
      rw [h1, b.repr_sum_self]
    have h3 : b.repr (a y) i = lam * b.repr y i := by
      rw [hy, map_smul]; rfl
    rw [h2] at h3
    simp only at h3
    rw [mul_comm, h3]
  have hsum : ∑ i, b.repr y i • b i = y := b.sum_repr y
  rw [← hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : μ i = lam
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  · have : b.repr y i = 0 := by
      have h4 := hrepr i
      by_contra hne
      exact hi (mul_right_cancel₀ hne h4)
    simp [this]

theorem finrank_classSpan_le [FiniteDimensional K V] {a : Module.End K V}
    (ha : ∀ i, a (b i) = μ i • b i) (β : V ≃ₗ[K] V) {c : K}
    (hrel : ∀ v, a (β v) = c • β (a v)) (lam : K) :
    finrank K (classSpan b μ lam) ≤ finrank K (classSpan b μ (c * lam)) := by
  have hmap : ∀ x ∈ classSpan b μ lam, β x ∈ classSpan b μ (c * lam) := by
    intro x hx
    refine mem_classSpan_of_eigen ha ?_
    rw [hrel, eigen_of_mem_classSpan ha hx, map_smul, smul_smul]
  let g : classSpan b μ lam →ₗ[K] classSpan b μ (c * lam) :=
    (β.toLinearMap.restrict hmap)
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply β.injective
    exact congrArg Subtype.val hxy
  exact LinearMap.finrank_le_finrank_of_injective hg

theorem card_class_eq [FiniteDimensional K V] {a : Module.End K V}
    (ha : ∀ i, a (b i) = μ i • b i) (β : V ≃ₗ[K] V) {c : K} (hc : c ≠ 0)
    (hrel : ∀ v, a (β v) = c • β (a v)) (lam : K) :
    Nat.card {i // μ i = c * lam} = Nat.card {i // μ i = lam} := by
  have h1 := finrank_classSpan_le ha β hrel lam
  have hrel' : ∀ v, a (β.symm v) = c⁻¹ • β.symm (a v) := by
    intro v
    have h2 := hrel (β.symm v)
    rw [LinearEquiv.apply_symm_apply] at h2
    have h3 : β.symm (a v) = c • a (β.symm v) := by
      rw [h2, map_smul, LinearEquiv.symm_apply_apply]
    rw [h3, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h4 := finrank_classSpan_le ha β.symm hrel' (c * lam)
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at h4
  rw [finrank_classSpan, finrank_classSpan] at h1 h4
  omega

end Classes

section Partner

variable {b : Basis ι K V} {μ : ι → K}

theorem exists_partner [FiniteDimensional K V] {a : Module.End K V}
    (ha : ∀ i, a (b i) = μ i • b i) (β : V ≃ₗ[K] V) {c : K} {p : ℕ} (hp : p.Prime)
    (hc : IsPrimitiveRoot c p) (hrel : ∀ v, a (β v) = c • β (a v)) (hμ : ∀ i, μ i ^ p = 1)
    (hn : 2 * p ≤ Fintype.card ι) (i : ι) : ∃ j, j ≠ i ∧ μ j = μ i := by
  classical
  have hc0 : c ≠ 0 := hc.ne_zero hp.ne_zero
  set lam0 := μ i with hlam0
  have hlp : lam0 ^ p = 1 := hμ i
  have : NeZero p := ⟨hp.ne_zero⟩
  have hlam00 : lam0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hlp
    exact zero_ne_one hlp
  have hs : ∀ k : ℕ, Nat.card {j // μ j = c ^ k * lam0} = Nat.card {j // μ j = lam0} := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, card_class_eq ha β hc0 hrel, ih]
  set T : Finset K := (Finset.range p).image (fun k => c ^ k * lam0) with hT
  have hinj : Set.InjOn (fun k : ℕ => c ^ k * lam0) (Finset.range p : Set ℕ) := by
    intro k hk l hl hkl
    have hkl' : c ^ k = c ^ l := mul_right_cancel₀ hlam00 hkl
    exact hc.pow_inj (by simpa using hk) (by simpa using hl) hkl'
  have hTcard : T.card = p := by
    rw [hT, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hmem : ∀ j, μ j ∈ T := by
    intro j
    have h1 : (μ j / lam0) ^ p = 1 := by rw [div_pow, hμ j, hlp, div_one]
    obtain ⟨k, hk, hk'⟩ := hc.eq_pow_of_pow_eq_one h1
    rw [hT, Finset.mem_image]
    exact ⟨k, Finset.mem_range.mpr hk, by rw [hk', div_mul_cancel₀ _ hlam00]⟩
  have hsum := Finset.card_eq_sum_card_fiberwise (f := μ) (s := (Finset.univ : Finset ι)) (t := T)
    (fun j _ => hmem j)
  have hfib : ∀ lam : K, (Finset.univ.filter fun j => μ j = lam).card =
      Nat.card {j // μ j = lam} := by
    intro lam
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum' : Fintype.card ι = p * Nat.card {j // μ j = lam0} := by
    rw [← Finset.card_univ, hsum, hT, Finset.sum_image hinj]
    simp only [hfib, hs]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h2 : 2 ≤ Nat.card {j // μ j = lam0} := by
    by_contra hlt
    push Not at hlt
    have : Nat.card {j // μ j = lam0} ≤ 1 := by omega
    have := Nat.mul_le_mul_left p this
    have := hp.two_le
    omega
  have h3 : 1 < Fintype.card {j // μ j = lam0} := by
    rw [← Nat.card_eq_fintype_card]; omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card h3 ⟨i, rfl⟩
  exact ⟨j.1, fun h' => hj (Subtype.ext h'), j.2⟩

end Partner

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
