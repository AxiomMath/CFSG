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

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem pow_48_eq_one_of_transvections {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {α β : MulAut V}
    (hα : ∃ x : V, ∀ v : V, α v = v ∨ α v = v * x)
    (hβ : ∃ y : V, ∀ v : V, β v = v ∨ β v = v * y) :
    (α * β) ^ 48 = 1 := by
  classical
  obtain ⟨x, hx⟩ := hα
  obtain ⟨y, hy⟩ := hβ
  obtain ⟨S, hS⟩ : ∃ S : Finset V, S = {1, x, y, x * y} := ⟨_, rfl⟩
  have hmem : ∀ s : V, s ∈ S ↔ s = 1 ∨ s = x ∨ s = y ∨ s = x * y := by
    intro s
    rw [hS]
    simp
  have m1 : (1 : V) ∈ S := (hmem 1).2 (Or.inl rfl)
  have mx : x ∈ S := (hmem x).2 (Or.inr (Or.inl rfl))
  have my : y ∈ S := (hmem y).2 (Or.inr (Or.inr (Or.inl rfl)))
  have mxy : x * y ∈ S := (hmem (x * y)).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hcard : S.card ≤ 4 := by
    rw [hS]
    exact Finset.card_le_four
  have hxx : x * x = 1 := hV x
  have hyy : y * y = 1 := hV y
  have e1 : x * (x * y) = y := by rw [← mul_assoc, hxx, one_mul]
  have e2 : y * (x * y) = x := by rw [mul_left_comm, hyy, mul_one]
  have e3 : x * y * x = y := by rw [mul_comm (x * y) x, e1]
  have e4 : x * y * y = x := by rw [mul_assoc, hyy, mul_one]
  have e5 : x * y * (x * y) = 1 := hV _
  have hyx : y * x = x * y := mul_comm y x
  have hmul : ∀ s ∈ S, ∀ t ∈ S, s * t ∈ S := by
    intro s hs t ht
    rw [hmem] at hs ht ⊢
    rcases hs with h | h | h | h <;> rcases ht with h' | h' | h' | h' <;>
      simp [h, h', hxx, hyy, e1, e2, e3, e4, e5, hyx]
  obtain ⟨c, hc⟩ : ∃ c : MulAut V, c = α * β := ⟨_, rfl⟩
  have hc' : ∀ v : V, c v = α (β v) := fun v => by rw [hc, MulAut.mul_apply]
  have h1 : ∀ v : V, ∃ s ∈ S, c v = v * s := by
    intro v
    rw [hc']
    rcases hy v with hb | hb
    · rw [hb]
      rcases hx v with ha | ha
      · exact ⟨1, m1, by rw [ha, mul_one]⟩
      · exact ⟨x, mx, ha⟩
    · rw [hb, map_mul]
      rcases hx v with ha | ha <;> rcases hx y with hy' | hy'
      · exact ⟨y, my, by rw [ha, hy']⟩
      · exact ⟨x * y, mxy, by rw [ha, hy', hyx]⟩
      · exact ⟨x * y, mxy, by rw [ha, hy', mul_assoc]⟩
      · exact ⟨y, my, by rw [ha, hy', mul_mul_mul_comm, hxx, mul_one]⟩
  have hcS : ∀ s ∈ S, c s ∈ S := by
    intro s hs
    obtain ⟨t, ht, hct⟩ := h1 s
    rw [hct]
    exact hmul s hs t ht
  have h2 : ∀ k : ℕ, ∀ v : V, ∃ s ∈ S, (c ^ k) v = v * s := by
    intro k
    induction k with
    | zero => intro v; exact ⟨1, m1, by simp⟩
    | succ k ih =>
      intro v
      obtain ⟨s, hs, hv⟩ := ih v
      obtain ⟨t, ht, hct⟩ := h1 v
      refine ⟨t * c s, hmul t ht (c s) (hcS s hs), ?_⟩
      rw [pow_succ', MulAut.mul_apply, hv, map_mul, hct, mul_assoc]
  have hg : Function.Injective (fun s : S => (⟨c s, hcS s s.2⟩ : S)) := by
    intro s t hst
    apply Subtype.ext
    apply c.injective
    exact congrArg Subtype.val hst
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm S, ∀ s : S, (σ s : V) = c s :=
    ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hg), fun s => rfl⟩
  have hσpow : ∀ n : ℕ, ∀ s : S, ((σ ^ n) s : V) = (c ^ n) (s : V) := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      simp only [pow_succ', Equiv.Perm.mul_apply, MulAut.mul_apply, hσ, ih]
  have hσ24 : σ ^ 24 = 1 := by
    have hdvd : Fintype.card (Equiv.Perm S) ∣ 24 := by
      rw [Fintype.card_perm, Fintype.card_coe]
      exact (Nat.factorial_dvd_factorial hcard).trans (by decide)
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_card.trans hdvd)
  have hfix : ∀ s ∈ S, (c ^ 24) s = s := by
    intro s hs
    have h := hσpow 24 ⟨s, hs⟩
    rw [hσ24] at h
    simpa using h.symm
  rw [← hc]
  ext v
  obtain ⟨s₀, hs₀, hv⟩ := h2 24 v
  rw [MulAut.one_apply, show (48 : ℕ) = 24 + 24 from rfl, pow_add, MulAut.mul_apply, hv, map_mul,
    hv, hfix s₀ hs₀, mul_assoc, hV s₀, mul_one]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
