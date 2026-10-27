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

namespace CFSG.LargeExtraspecial.S14

open Subgroup

section Count

variable {G : Type*} [Group G]

theorem comm_mul_eq (τ n m : G) :
    τ⁻¹ * (n * m)⁻¹ * τ * (n * m) = (τ⁻¹ * m⁻¹ * τ * m) * (m⁻¹ * (τ⁻¹ * n⁻¹ * τ * n) * m) := by
  group

theorem false_of_commutator_count_aux {N B K : Subgroup G} {t : G} (c : G → G)
    (hcm : ∀ n ∈ N, ∀ m ∈ N, c (n * m) = c m * (m⁻¹ * c n * m))
    (htN : ∀ n ∈ N, n * t = t * n) (htt : t * t = 1) (ht1 : t ≠ 1)
    (hconj : ∀ k ∈ K, ∀ n ∈ N, n⁻¹ * k * n = k ∨ n⁻¹ * k * n = k * t)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (htB : t ∈ B) (hKB : K ≤ B)
    (hsurj : ∀ k ∈ K, ∃ n ∈ N, c n = k ∨ c n = k * t)
    (hK1 : ∀ n ∈ N, c n ∈ K → c n = 1)
    {k₁ k₂ k₃ : G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (hk₃ : k₃ ∈ K) (h1 : k₁ ≠ 1) (h2 : k₂ ≠ 1)
    (h3 : k₃ ≠ 1) (h12 : k₁ * k₂ ≠ 1) (h23 : k₂ * k₃ ≠ 1) (h13 : k₁ * k₃ ≠ 1)
    (h123 : k₁ * k₂ * k₃ ≠ 1) : False := by
  have htt' : ∀ x : G, x * t * t = x := fun x => by rw [mul_assoc, htt, mul_one]
  have hlift : ∀ k ∈ K, k ≠ 1 → ∃ n ∈ N, c n = k * t := by
    intro k hk hk1
    obtain ⟨n, hn, h | h⟩ := hsurj k hk
    · exact absurd ((hK1 n hn (h ▸ hk)).symm.trans h) (Ne.symm hk1)
    · exact ⟨n, hn, h⟩
  have hconj' : ∀ k ∈ K, ∀ m ∈ N, m⁻¹ * (k * t) * m = m⁻¹ * k * m * t := by
    intro k _ m hm
    have : m⁻¹ * t * m = t := by
      rw [mul_assoc, ← htN m hm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [show m⁻¹ * (k * t) * m = m⁻¹ * k * m * (m⁻¹ * t * m) by group, this]
  have hstep : ∀ k ∈ K, ∀ k' ∈ K, ∀ n ∈ N, ∀ m ∈ N, c n = k * t → c m = k' * t → k * k' ≠ 1 →
      m⁻¹ * k * m = k * t ∧ c (n * m) = k * k' * t := by
    intro k hk k' hk' n hn m hm hn' hm' hkk'
    have hjB : m⁻¹ * k * m ∈ B := by
      rcases hconj k hk m hm with h | h
      · rw [h]; exact hKB hk
      · rw [h]; exact B.mul_mem (hKB hk) htB
    have e : c (n * m) = k' * (m⁻¹ * k * m) := by
      rw [hcm n hn m hm, hn', hm', hconj' k hk m hm]
      calc k' * t * (m⁻¹ * k * m * t) = k' * (t * (m⁻¹ * k * m)) * t := by group
        _ = k' * (m⁻¹ * k * m) := by rw [hB t htB _ hjB, mul_assoc, mul_assoc, htt, mul_one]
    rcases hconj k hk m hm with h | h
    · rw [h, hB k' (hKB hk') k (hKB hk)] at e
      have h0 := hK1 (n * m) (N.mul_mem hn hm) (e ▸ K.mul_mem hk hk')
      exact absurd (e.symm.trans h0) hkk'
    · refine ⟨h, ?_⟩
      rw [e, h, ← mul_assoc, hB k' (hKB hk') k (hKB hk)]
  obtain ⟨n₁, hn₁, e₁⟩ := hlift k₁ hk₁ h1
  obtain ⟨n₂, hn₂, e₂⟩ := hlift k₂ hk₂ h2
  obtain ⟨n₃, hn₃, e₃⟩ := hlift k₃ hk₃ h3
  obtain ⟨a₂, -⟩ := hstep k₁ hk₁ k₂ hk₂ n₁ hn₁ n₂ hn₂ e₁ e₂ h12
  obtain ⟨a₃, -⟩ := hstep k₁ hk₁ k₃ hk₃ n₁ hn₁ n₃ hn₃ e₁ e₃ h13
  obtain ⟨-, e₂₃⟩ := hstep k₂ hk₂ k₃ hk₃ n₂ hn₂ n₃ hn₃ e₂ e₃ h23
  have h1' : k₁ * (k₂ * k₃) ≠ 1 := by rwa [← mul_assoc]
  obtain ⟨a₂₃, -⟩ := hstep k₁ hk₁ (k₂ * k₃) (K.mul_mem hk₂ hk₃) n₁ hn₁ (n₂ * n₃)
    (N.mul_mem hn₂ hn₃) e₁ e₂₃ h1'
  have e : (n₂ * n₃)⁻¹ * k₁ * (n₂ * n₃) = k₁ := by
    rw [show (n₂ * n₃)⁻¹ * k₁ * (n₂ * n₃) = n₃⁻¹ * (n₂⁻¹ * k₁ * n₂) * n₃ by group, a₂,
      hconj' k₁ hk₁ n₃ hn₃, a₃, htt']
  rw [e] at a₂₃
  apply ht1
  calc t = k₁⁻¹ * (k₁ * t) := by group
    _ = 1 := by rw [← a₂₃, inv_mul_cancel]

theorem false_of_commutator_count {N B K : Subgroup G} {τ t : G} (htN : ∀ n ∈ N, n * t = t * n)
    (htt : t * t = 1) (ht1 : t ≠ 1)
    (hconj : ∀ k ∈ K, ∀ n ∈ N, n⁻¹ * k * n = k ∨ n⁻¹ * k * n = k * t)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (htB : t ∈ B) (hKB : K ≤ B)
    (hsurj : ∀ k ∈ K, ∃ n ∈ N, τ⁻¹ * n⁻¹ * τ * n = k ∨ τ⁻¹ * n⁻¹ * τ * n = k * t)
    (hK1 : ∀ n ∈ N, τ⁻¹ * n⁻¹ * τ * n ∈ K → τ⁻¹ * n⁻¹ * τ * n = 1)
    {k₁ k₂ k₃ : G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (hk₃ : k₃ ∈ K) (h1 : k₁ ≠ 1) (h2 : k₂ ≠ 1)
    (h3 : k₃ ≠ 1) (h12 : k₁ * k₂ ≠ 1) (h23 : k₂ * k₃ ≠ 1) (h13 : k₁ * k₃ ≠ 1)
    (h123 : k₁ * k₂ * k₃ ≠ 1) : False :=
  false_of_commutator_count_aux (fun n => τ⁻¹ * n⁻¹ * τ * n)
    (fun n _ m _ => comm_mul_eq τ n m) htN htt ht1 hconj hB htB hKB hsurj hK1 hk₁ hk₂ hk₃
    h1 h2 h3 h12 h23 h13 h123

end Count

end CFSG.LargeExtraspecial.S14
