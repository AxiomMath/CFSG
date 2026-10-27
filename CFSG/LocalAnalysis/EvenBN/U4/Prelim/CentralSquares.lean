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

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup

variable {Γ : Type*} [Group Γ]

theorem sq_mem_and_commutator_mem_of_transitive {N Z S : Subgroup Γ} (hNZ : N ≤ Z)
    (hZS : Z ≤ S) (hSN : S ≤ normalizer (N : Set Γ))
    (hZ2 : ∀ a ∈ Z, ∀ b ∈ Z, a ∉ N → b ∉ N → a * b ∈ N)
    (hZc : ∀ s ∈ S, ∀ a ∈ Z, s * a * s⁻¹ * a⁻¹ ∈ N)
    (hsq : ∀ s ∈ S, s * s ∈ Z)
    (hcomm : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ Z)
    (htr : ∀ s ∈ S, s ∉ Z → ∀ s' ∈ S, s' ∉ Z → ∃ g : Γ, (∀ a ∈ Z, g * a * g⁻¹ * a⁻¹ ∈ N) ∧
      g * s * g⁻¹ ∈ S ∧ (g * s * g⁻¹) * s'⁻¹ ∈ Z)
    (hdim : ∃ x ∈ S, ∃ y ∈ S, ∃ w ∈ S, x ∉ Z ∧ y ∉ Z ∧ x * y ∉ Z ∧ x * w ∉ Z ∧ y * w ∉ Z ∧
      x * (y * w) ∉ Z ∧ w ∉ Z) :
    (∀ s ∈ S, s * s ∈ N) ∧ ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ N := by
  classical
  let par : Γ → ZMod 2 := fun a => if a ∈ N then 0 else 1
  have hparN : ∀ a, a ∈ N → par a = 0 := fun a ha => ite_eq_left ha
  have hpar0 : ∀ a, par a = 0 → a ∈ N := fun a h => by
    by_contra ha
    have : par a = 1 := ite_eq_right ha
    rw [this] at h
    exact one_ne_zero h
  have hpar_mul : ∀ a ∈ Z, ∀ b ∈ Z, par (a * b) = par a + par b := by
    intro a ha b hb
    by_cases haN : a ∈ N <;> by_cases hbN : b ∈ N
    · rw [hparN _ (mul_mem haN hbN), hparN _ haN, hparN _ hbN, add_zero]
    · have hab : a * b ∉ N := fun h => hbN (by simpa using mul_mem (inv_mem haN) h)
      change (if a * b ∈ N then (0 : ZMod 2) else 1) =
        (if a ∈ N then (0 : ZMod 2) else 1) + (if b ∈ N then (0 : ZMod 2) else 1)
      rw [ite_eq_right hab, ite_eq_left haN, ite_eq_right hbN, zero_add]
    · have hab : a * b ∉ N := fun h => haN (by simpa using mul_mem h (inv_mem hbN))
      change (if a * b ∈ N then (0 : ZMod 2) else 1) =
        (if a ∈ N then (0 : ZMod 2) else 1) + (if b ∈ N then (0 : ZMod 2) else 1)
      rw [ite_eq_right hab, ite_eq_right haN, ite_eq_left hbN, add_zero]
    · change (if a * b ∈ N then (0 : ZMod 2) else 1) =
        (if a ∈ N then (0 : ZMod 2) else 1) + (if b ∈ N then (0 : ZMod 2) else 1)
      rw [ite_eq_left (hZ2 a ha b hb haN hbN), ite_eq_right haN, ite_eq_right hbN]
      decide
  have hZmul : ∀ a ∈ Z, ∀ b ∈ Z, a * b ∈ Z := fun a ha b hb => mul_mem ha hb
  have hconjN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N := fun s hs n hn =>
    (mem_normalizer_iff.1 (hSN hs) n).1 hn
  have hcm : ∀ x ∈ S, ∀ y ∈ S, y⁻¹ * x⁻¹ * y * x ∈ Z := fun x hx y hy => by
    have := hcomm y⁻¹ (inv_mem hy) x⁻¹ (inv_mem hx)
    rwa [inv_inv, inv_inv] at this
  have hsq_mul : ∀ x ∈ S, ∀ y ∈ S, par ((x * y) * (x * y)) =
      par (x * x) + par (y⁻¹ * x⁻¹ * y * x) + par (y * y) := by
    intro x hx y hy
    set c := y⁻¹ * x⁻¹ * y * x with hc
    have hcZ : c ∈ Z := hcm x hx y hy
    have hn : y * c * y⁻¹ * c⁻¹ ∈ N := hZc y hy c hcZ
    have e : (x * y) * (x * y) = (x * x) * ((y * c * y⁻¹ * c⁻¹) * (c * (y * y))) := by
      rw [hc]; group
    rw [e, hpar_mul _ (hsq x hx) _ (hZmul _ (hNZ hn) _ (hZmul _ hcZ _ (hsq y hy))),
      hpar_mul _ (hNZ hn) _ (hZmul _ hcZ _ (hsq y hy)), hpar_mul _ hcZ _ (hsq y hy),
      hparN _ hn, zero_add, add_assoc]
  have hcm_mul : ∀ x ∈ S, ∀ y ∈ S, ∀ w ∈ S, par ((y * w)⁻¹ * x⁻¹ * (y * w) * x) =
      par (y⁻¹ * x⁻¹ * y * x) + par (w⁻¹ * x⁻¹ * w * x) := by
    intro x hx y hy w hw
    set c := y⁻¹ * x⁻¹ * y * x with hc
    have hcZ : c ∈ Z := hcm x hx y hy
    have hn : w⁻¹ * c * w * c⁻¹ ∈ N := by
      have := hZc w⁻¹ (inv_mem hw) c hcZ
      rwa [inv_inv] at this
    have e : (y * w)⁻¹ * x⁻¹ * (y * w) * x =
        (w⁻¹ * c * w * c⁻¹) * (c * (w⁻¹ * x⁻¹ * w * x)) := by
      rw [hc]; group
    rw [e, hpar_mul _ (hNZ hn) _ (hZmul _ hcZ _ (hcm x hx w hw)), hpar_mul _ hcZ _ (hcm x hx w hw),
      hparN _ hn, zero_add]
  have hpar_conj : ∀ g : Γ, (∀ a ∈ Z, g * a * g⁻¹ * a⁻¹ ∈ N) → ∀ a ∈ Z,
      par (g * a * g⁻¹) = par a := by
    intro g hg a ha
    have hn := hg a ha
    have e : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
    rw [e, hpar_mul _ (hNZ hn) _ ha, hparN _ hn, zero_add]
  have hsq_Z : ∀ s ∈ S, ∀ z ∈ Z, par ((z * s) * (z * s)) = par (s * s) := by
    intro s hs z hz
    have hzz : par (z * z) = 0 := by
      rw [hpar_mul _ hz _ hz]
      by_cases hzN : z ∈ N
      · rw [hparN _ hzN, add_zero]
      · change (if z ∈ N then (0 : ZMod 2) else 1) + (if z ∈ N then (0 : ZMod 2) else 1) = 0
        rw [ite_eq_right hzN]
        decide
    have hn : s⁻¹ * z⁻¹ * s * z ∈ N := by
      have := hZc s⁻¹ (inv_mem hs) z⁻¹ (inv_mem hz)
      rwa [inv_inv, inv_inv] at this
    rw [hsq_mul z (hZS hz) s hs, hzz, hparN _ hn, zero_add, zero_add]
  obtain ⟨x, hx, y, hy, w, hw, hxZ, hyZ, hxyZ, hxwZ, hywZ, hxywZ, hwZ⟩ := hdim
  have hconst : ∀ u ∈ S, u ∉ Z → par (u * u) = par (x * x) := by
    intro u hu huZ
    obtain ⟨g, hgZ, hgS, hgx⟩ := htr u hu huZ x hx hxZ
    set z := (g * u * g⁻¹) * x⁻¹ with hz
    have e : g * u * g⁻¹ = z * x := by rw [hz]; group
    have h1 : par ((g * u * g⁻¹) * (g * u * g⁻¹)) = par (u * u) := by
      rw [show (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ by group]
      exact hpar_conj g hgZ _ (hsq u hu)
    rw [← h1, e, hsq_Z x hx z hgx]
  have hc0 : par (x * x) = 0 := by
    have hyx : par (y⁻¹ * x⁻¹ * y * x) = par (x * x) := by
      have := hsq_mul x hx y hy
      rw [hconst _ (mul_mem hx hy) hxyZ, hconst y hy hyZ] at this
      have h2 : (2 : ZMod 2) = 0 := rfl
      linear_combination -this - par (x * x) * h2
    have hwx : par (w⁻¹ * x⁻¹ * w * x) = par (x * x) := by
      have := hsq_mul x hx w hw
      rw [hconst _ (mul_mem hx hw) hxwZ, hconst w hw hwZ] at this
      have h2 : (2 : ZMod 2) = 0 := rfl
      linear_combination -this - par (x * x) * h2
    have hywx : par ((y * w)⁻¹ * x⁻¹ * (y * w) * x) = par (x * x) := by
      have := hsq_mul x hx (y * w) (mul_mem hy hw)
      rw [hconst _ (mul_mem hx (mul_mem hy hw)) hxywZ,
        hconst _ (mul_mem hy hw) hywZ] at this
      have h2 : (2 : ZMod 2) = 0 := rfl
      linear_combination -this - par (x * x) * h2
    have := hcm_mul x hx y hy w hw
    rw [hywx, hyx, hwx] at this
    have h2 : (2 : ZMod 2) = 0 := rfl
    linear_combination this + par (x * x) * h2
  have hsqN : ∀ s ∈ S, s * s ∈ N := by
    intro s hs
    refine hpar0 _ ?_
    by_cases hsZ : s ∈ Z
    · rw [hpar_mul _ hsZ _ hsZ]
      by_cases hsN : s ∈ N
      · rw [hparN _ hsN, add_zero]
      · change (if s ∈ N then (0 : ZMod 2) else 1) + (if s ∈ N then (0 : ZMod 2) else 1) = 0
        rw [ite_eq_right hsN]
        decide
    · rw [hconst s hs hsZ, hc0]
  refine ⟨hsqN, fun s hs s' hs' => hpar0 _ ?_⟩
  have := hsq_mul s'⁻¹ (inv_mem hs') s⁻¹ (inv_mem hs)
  rw [hparN _ (hsqN _ (mul_mem (inv_mem hs') (inv_mem hs))), hparN _ (hsqN _ (inv_mem hs')),
    hparN _ (hsqN _ (inv_mem hs)), inv_inv, inv_inv] at this
  linear_combination -this

end CFSG.LocalAnalysis.EvenBN.U4
