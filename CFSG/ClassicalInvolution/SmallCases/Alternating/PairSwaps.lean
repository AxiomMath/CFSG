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
public import Mathlib.GroupTheory.GroupAction.Period
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.ClassicalInvolution

open Equiv

variable {n : ℕ}

@[expose] def pairSwaps (z : Perm (Fin n)) (hz : z * z = 1) : Subgroup (Perm (Fin n)) where
  carrier := {w | ∀ a, w a = a ∨ w a = z a}
  mul_mem' := by
    intro v w hv hw a
    have hzz : ∀ b, z (z b) = b := fun b => by simpa using congrArg (fun p : Perm (Fin n) => p b) hz
    rcases hw a with h | h
    · rcases hv a with h' | h'
      · left; simp [Perm.mul_apply, h, h']
      · right; simp [Perm.mul_apply, h, h']
    · rcases hv (z a) with h' | h'
      · right; simp [Perm.mul_apply, h, h']
      · left; simp [Perm.mul_apply, h, h', hzz]
  one_mem' := fun a => Or.inl rfl
  inv_mem' := by
    intro w hw a
    have hzz : ∀ b, z (z b) = b := fun b => by simpa using congrArg (fun p : Perm (Fin n) => p b) hz
    have h1 : w (w⁻¹ a) = a := by simp
    rcases hw (w⁻¹ a) with h | h
    · left
      rw [h1] at h
      exact h.symm
    · right
      rw [h1] at h
      have h2 := congrArg z h
      rw [hzz] at h2
      exact h2.symm

section PairSwapsFacts

variable {z : Perm (Fin n)} {hz : z * z = 1}

theorem mem_pairSwaps {w : Perm (Fin n)} :
    w ∈ pairSwaps z hz ↔ ∀ a, w a = a ∨ w a = z a := Iff.rfl

theorem z_mem_pairSwaps : z ∈ pairSwaps z hz := fun _ => Or.inr rfl

theorem swap_mem_pairSwaps (x : Fin n) : Equiv.swap x (z x) ∈ pairSwaps z hz := by
  have hzz : ∀ b, z (z b) = b := fun b => by simpa using congrArg (fun p : Perm (Fin n) => p b) hz
  intro a
  rw [Equiv.swap_apply_def]
  by_cases h1 : a = x
  · right; simp [h1]
  · by_cases h2 : a = z x
    · right; simp [h2, hzz]
    · left; simp [h1, h2]

theorem pairSwaps_apply_z {w : Perm (Fin n)} (hw : w ∈ pairSwaps z hz) (a : Fin n) :
    w (z a) = z (w a) := by
  have hzz : ∀ b, z (z b) = b := fun b => by simpa using congrArg (fun p : Perm (Fin n) => p b) hz
  have inj := w.injective
  rcases hw a with h | h
  · rcases hw (z a) with h' | h'
    · rw [h, h']
    · have h'' : w (z a) = a := by rw [h', hzz]
      have hza : z a = a := inj (h''.trans h.symm)
      rw [h, hza]
      exact h
  · rcases hw (z a) with h' | h'
    · have hza : z a = a := inj (h'.trans h.symm)
      rw [h]
      rw [hza]
      exact h
    · rw [h, h']

theorem pairSwaps_mul_self {w : Perm (Fin n)} (hw : w ∈ pairSwaps z hz) : w * w = 1 := by
  have hzz : ∀ b, z (z b) = b := fun b => by simpa using congrArg (fun p : Perm (Fin n) => p b) hz
  ext a
  rcases hw a with h | h
  · simp [Perm.mul_apply, h]
  · simp [Perm.mul_apply, h, pairSwaps_apply_z hw, hzz]

theorem conj_mem_pairSwaps {w c : Perm (Fin n)} (hw : w ∈ pairSwaps z hz) (hc : c * z = z * c) :
    c * w * c⁻¹ ∈ pairSwaps z hz := by
  have hcz : ∀ b, c (z b) = z (c b) := fun b => by
    simpa using congrArg (fun p : Perm (Fin n) => p b) hc
  intro a
  have hc1 : c (c⁻¹ a) = a := by simp
  rw [Perm.mul_apply, Perm.mul_apply]
  rcases hw (c⁻¹ a) with h | h
  · left
    rw [h, hc1]
  · right
    rw [h, hcz, hc1]

theorem apply_eq_self_of_pow_two_pow {α : Type*} {g : Perm α} (hg : Odd (orderOf g)) (j : ℕ)
    {a : α} (h : (g ^ 2 ^ j) a = a) : g a = a := by
  have h1 : MulAction.period g a ∣ 2 ^ j :=
    MulAction.pow_smul_eq_iff_period_dvd.mp (by simpa using h)
  have h2 : MulAction.period g a ∣ orderOf g := MulAction.period_dvd_orderOf g a
  have hcop : Nat.Coprime (2 ^ j) (orderOf g) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hg)
  have h3 : MulAction.period g a = 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop, Nat.dvd_one] at this
  simpa using (MulAction.period_eq_one_iff.mp h3)

theorem exists_mem_pairSwaps_not_commute (g : Perm (Fin n)) (hgz : g * z = z * g)
    (hg : Odd (orderOf g)) {a : Fin n} (ha : z a ≠ a) (hga : g a ≠ a) :
    ∃ u ∈ pairSwaps z hz, Perm.sign u = 1 ∧ u * g ≠ g * u := by
  have hzz : ∀ b, z (z b) = b := fun b => by simpa using congrArg (fun p : Perm (Fin n) => p b) hz
  have hgzx : ∀ b, g (z b) = z (g b) := fun b => by
    simpa using congrArg (fun p : Perm (Fin n) => p b) hgz
  have hginj := g.injective
  have hzinj := z.injective
  have hga2 : g (g a) ≠ a := by
    intro h
    apply hga
    exact apply_eq_self_of_pow_two_pow hg 1 (by simpa [pow_two, Perm.mul_apply] using h)
  have hbza : g a ≠ z a := by
    intro h
    apply hga2
    rw [h, hgzx, h, hzz]
  have hgz2 : g (g a) ≠ z a := by
    intro h
    apply hga
    have h4 : (g ^ 2 ^ 2) a = a := by
      have : g (g (g (g a))) = a := by rw [h, hgzx, hgzx, h, hzz]
      simpa [pow_succ, Perm.mul_apply] using this
    exact apply_eq_self_of_pow_two_pow hg 2 h4
  have hzb : z (g a) ≠ g a := by
    intro h
    apply ha
    rw [← hgzx] at h
    exact hginj h
  have hzga : z (g a) ≠ a := by
    intro h
    apply hbza
    have := congrArg z h
    rwa [hzz] at this
  have hzgza : z (g a) ≠ z a := fun h => hga (hzinj h)
  have hggb : g (g a) ≠ g a := fun h => hga (hginj h)
  have hggzb : g (g a) ≠ z (g a) := by
    intro h
    apply hbza
    rw [← hgzx] at h
    exact hginj h
  refine ⟨Equiv.swap a (z a) * Equiv.swap (g a) (z (g a)),
    mul_mem (swap_mem_pairSwaps a) (swap_mem_pairSwaps (g a)), ?_, ?_⟩
  · rw [Perm.sign_mul, Perm.sign_swap (Ne.symm ha), Perm.sign_swap (Ne.symm hzb)]
    rfl
  · intro h
    have h' := congrArg (fun p : Perm (Fin n) => p (g a)) h
    simp only [Perm.mul_apply] at h'
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hzga hzgza,
      Equiv.swap_apply_of_ne_of_ne hggb hggzb,
      Equiv.swap_apply_of_ne_of_ne hga2 hgz2, hgzx] at h'
    have e : z (g (g a)) = g (g (z a)) := by rw [← hgzx, ← hgzx]
    have h'' : g (g (z a)) = g (g a) := by rw [← e]; exact h'.symm
    exact ha (hginj (hginj h''))

end PairSwapsFacts

end CFSG.ClassicalInvolution
