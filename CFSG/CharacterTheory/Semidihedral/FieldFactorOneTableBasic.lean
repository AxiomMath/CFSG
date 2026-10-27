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
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

open Finset

namespace CFSG.Semidihedral.FieldFactorOne

namespace TableCoordinates

variable {L : Type*} [DecidableEq L]

theorem sign_mul_self {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) : δ * δ = 1 := by
  rcases hδ with rfl | rfl <;> norm_num

theorem sign_ne_zero {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) : δ ≠ 0 := by
  rcases hδ with rfl | rfl <;> norm_num

theorem one_le_mul_self_of_ne_zero {u : ℤ} (h : u ≠ 0) : 1 ≤ u * u := by
  have := mul_self_pos.mpr h
  omega

theorem eq_zero_or_one_or_neg_one {u : ℤ} (h : u * u ≤ 1) : u = 0 ∨ u = 1 ∨ u = -1 := by
  have h1 : u ≤ 1 := by nlinarith
  have h2 : -1 ≤ u := by nlinarith
  omega

theorem mul_self_le_one_of_lt_four {u : ℤ} (h : u * u < 4) : u * u ≤ 1 := by
  have h1 : u ≤ 1 := by nlinarith
  have h2 : -1 ≤ u := by nlinarith
  rcases (by omega : u = -1 ∨ u = 0 ∨ u = 1) with rfl | rfl | rfl <;> norm_num

theorem four_le_mul_self_of_even {u : ℤ} (he : Even u) (h : u ≠ 0) : 4 ≤ u * u := by
  obtain ⟨m, rfl⟩ := he
  have hm : m ≠ 0 := by
    rintro rfl
    simp at h
  have := one_le_mul_self_of_ne_zero hm
  nlinarith

theorem eq_one_or_neg_one_of_odd {u : ℤ} (hu : Odd u) (h : u * u < 9) : u = 1 ∨ u = -1 := by
  obtain ⟨m, rfl⟩ := hu
  have h1 : -2 < m := by nlinarith
  have h2 : m < 1 := by nlinarith
  omega

theorem eq_zero_of_le_mul_self {s : Finset L} {f : L → ℤ} {a : L} (ha : a ∈ s) {c : ℤ}
    (hsum : ∑ x ∈ s, f x * f x = c) (hfa : c ≤ f a * f a) : ∀ x ∈ s, x ≠ a → f x = 0 := by
  have herase := Finset.add_sum_erase s (fun x => f x * f x) ha
  have hnn : ∀ x ∈ s.erase a, 0 ≤ f x * f x := fun x _ => mul_self_nonneg _
  have h0 : ∑ x ∈ s.erase a, f x * f x = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg hnn)
  intro x hx hxa
  exact mul_self_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 x (Finset.mem_erase.mpr ⟨hxa, hx⟩))

theorem exists_unique_ne_zero {s : Finset L} {f : L → ℤ} {c : ℤ} (hc : 0 < c)
    (hsum : ∑ x ∈ s, f x * f x = c) (hmin : ∀ x ∈ s, f x ≠ 0 → c ≤ f x * f x) :
    ∃ a ∈ s, f a * f a = c ∧ ∀ x ∈ s, x ≠ a → f x = 0 := by
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact hc.ne')
  have hfa : f a ≠ 0 := fun h => hne (by simp [h])
  have hrest := eq_zero_of_le_mul_self ha hsum (hmin a ha hfa)
  refine ⟨a, ha, ?_, hrest⟩
  have herase := Finset.add_sum_erase s (fun x => f x * f x) ha
  have h0 : ∑ x ∈ s.erase a, f x * f x = 0 := Finset.sum_eq_zero fun x hx => by
    rw [hrest x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx), mul_zero]
  linarith

omit [DecidableEq L] in
theorem sum_mul_self_eq_card {s : Finset L} {f : L → ℤ} (h : ∀ x ∈ s, f x * f x ≤ 1) :
    ∑ x ∈ s, f x * f x = #(s.filter fun x => f x ≠ 0) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun x hx => ?_
  by_cases h0 : f x = 0
  · simp [h0]
  · have h1 := one_le_mul_self_of_ne_zero h0
    have h2 := h x hx
    simp only [ne_eq, h0, not_false_eq_true, ↓reduceIte]
    omega

omit [DecidableEq L] in
theorem card_filter_eq_one_of_sum_eq_zero {s : Finset L} {p : L → ℤ}
    (hp : ∀ x ∈ s, p x = 1 ∨ p x = -1) (hsum : ∑ x ∈ s, p x = 0) :
    2 * #(s.filter fun x => p x = 1) = #s ∧ 2 * #(s.filter fun x => ¬p x = 1) = #s := by
  have hcard := Finset.card_filter_add_card_filter_not (s := s) (fun x => p x = 1)
  have hs := Finset.sum_filter_add_sum_filter_not s (fun x => p x = 1) p
  have h1 : ∑ x ∈ s.filter (fun x => p x = 1), p x = #(s.filter fun x => p x = 1) := by
    rw [Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2]
    simp
  have h2 : ∑ x ∈ s.filter (fun x => ¬p x = 1), p x = -#(s.filter fun x => ¬p x = 1) := by
    rw [Finset.sum_congr rfl fun x hx => ((hp x (Finset.mem_filter.mp hx).1).resolve_left
      (Finset.mem_filter.mp hx).2)]
    simp
  rw [h1, h2, hsum] at hs
  omega

theorem sum_mul_ite_eq {R : Type*} [CommRing R] {B : Finset L} (f : L → R) {c : L}
    (hc : c ∈ B) : ∑ x ∈ B, f x * (if x = c then 1 else 0) = f c := by
  simp [hc]

theorem sum_ite_eq_mul {R : Type*} [CommRing R] {B : Finset L} (f : L → R) {c : L}
    (hc : c ∈ B) : ∑ x ∈ B, (if x = c then 1 else 0) * f x = f c := by
  simp [hc]

structure ShapeA (B : Finset L) (Θ U : L → ℤ) (c₀ c₁ c₂ c₃ c₄ : L) (δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ) :
    Prop where
  h₀ : c₀ ∈ B
  h₁ : c₁ ∈ B
  h₂ : c₂ ∈ B
  h₃ : c₃ ∈ B
  h₄ : c₄ ∈ B
  n01 : c₀ ≠ c₁
  n02 : c₀ ≠ c₂
  n03 : c₀ ≠ c₃
  n04 : c₀ ≠ c₄
  n12 : c₁ ≠ c₂
  n13 : c₁ ≠ c₃
  n14 : c₁ ≠ c₄
  n23 : c₂ ≠ c₃
  n24 : c₂ ≠ c₄
  n34 : c₃ ≠ c₄
  s₀ : δ₀ = 1 ∨ δ₀ = -1
  s₁ : δ₁ = 1 ∨ δ₁ = -1
  s₂ : δ₂ = 1 ∨ δ₂ = -1
  s₃ : δ₃ = 1 ∨ δ₃ = -1
  s₄ : δ₄ = 1 ∨ δ₄ = -1
  hΘ : ∀ x ∈ B, Θ x = δ₀ * (if x = c₀ then 1 else 0) + δ₁ * (if x = c₁ then 1 else 0) +
    δ₂ * (if x = c₂ then 1 else 0) + δ₃ * (if x = c₃ then 1 else 0)
  hU : ∀ x ∈ B, U x = δ₀ * (if x = c₀ then 1 else 0) - δ₁ * (if x = c₁ then 1 else 0) +
    δ₂ * (if x = c₂ then 1 else 0) - δ₃ * (if x = c₃ then 1 else 0) +
    2 * δ₄ * (if x = c₄ then 1 else 0)

section ShapeA

variable {B : Finset L} {Θ U : L → ℤ} {c₀ c₁ c₂ c₃ c₄ : L} {δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ}

theorem ShapeA.sum_mul_Θ (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (f : L → ℤ) :
    ∑ x ∈ B, f x * Θ x = δ₀ * f c₀ + δ₁ * f c₁ + δ₂ * f c₂ + δ₃ * f c₃ := by
  rw [Finset.sum_congr rfl fun x hx => by rw [A.hΘ x hx]]
  simp [mul_add, Finset.sum_add_distrib, A.h₀, A.h₁, A.h₂, A.h₃]
  ring

theorem ShapeA.sum_Θ_mul (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (f : L → ℤ) :
    ∑ x ∈ B, Θ x * f x = δ₀ * f c₀ + δ₁ * f c₁ + δ₂ * f c₂ + δ₃ * f c₃ := by
  rw [← A.sum_mul_Θ f]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem ShapeA.sum_mul_U (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (f : L → ℤ) :
    ∑ x ∈ B, f x * U x =
      δ₀ * f c₀ - δ₁ * f c₁ + δ₂ * f c₂ - δ₃ * f c₃ + 2 * δ₄ * f c₄ := by
  rw [Finset.sum_congr rfl fun x hx => by rw [A.hU x hx]]
  simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, A.h₀, A.h₁, A.h₂,
    A.h₃, A.h₄]
  ring

theorem ShapeA.sum_U_mul (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (f : L → ℤ) :
    ∑ x ∈ B, U x * f x =
      δ₀ * f c₀ - δ₁ * f c₁ + δ₂ * f c₂ - δ₃ * f c₃ + 2 * δ₄ * f c₄ := by
  rw [← A.sum_mul_U f]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem ShapeA.swap02 (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) :
    ShapeA B Θ U c₂ c₁ c₀ c₃ c₄ δ₂ δ₁ δ₀ δ₃ δ₄ where
  h₀ := A.h₂
  h₁ := A.h₁
  h₂ := A.h₀
  h₃ := A.h₃
  h₄ := A.h₄
  n01 := A.n12.symm
  n02 := A.n02.symm
  n03 := A.n23
  n04 := A.n24
  n12 := A.n01.symm
  n13 := A.n13
  n14 := A.n14
  n23 := A.n03
  n24 := A.n04
  n34 := A.n34
  s₀ := A.s₂
  s₁ := A.s₁
  s₂ := A.s₀
  s₃ := A.s₃
  s₄ := A.s₄
  hΘ x hx := by rw [A.hΘ x hx]; ring
  hU x hx := by rw [A.hU x hx]; ring

theorem ShapeA.swap13 (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) :
    ShapeA B Θ U c₀ c₃ c₂ c₁ c₄ δ₀ δ₃ δ₂ δ₁ δ₄ where
  h₀ := A.h₀
  h₁ := A.h₃
  h₂ := A.h₂
  h₃ := A.h₁
  h₄ := A.h₄
  n01 := A.n03
  n02 := A.n02
  n03 := A.n01
  n04 := A.n04
  n12 := A.n23.symm
  n13 := A.n13.symm
  n14 := A.n34
  n23 := A.n12.symm
  n24 := A.n24
  n34 := A.n14
  s₀ := A.s₀
  s₁ := A.s₃
  s₂ := A.s₂
  s₃ := A.s₁
  s₄ := A.s₄
  hΘ x hx := by rw [A.hΘ x hx]; ring
  hU x hx := by rw [A.hU x hx]; ring

theorem ShapeA.five_subset (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) :
    ({c₀, c₁, c₂, c₃, c₄} : Finset L) ⊆ B := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [A.h₀, A.h₁, A.h₂, A.h₃, A.h₄]

theorem mem_sdiff_five {x c₀ c₁ c₂ c₃ c₄ : L} {B : Finset L} :
    x ∈ B \ {c₀, c₁, c₂, c₃, c₄} ↔
      x ∈ B ∧ x ≠ c₀ ∧ x ≠ c₁ ∧ x ≠ c₂ ∧ x ≠ c₃ ∧ x ≠ c₄ := by
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]

theorem ShapeA.sum_split (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (g : L → ℤ) :
    ∑ x ∈ B, g x =
      g c₀ + g c₁ + g c₂ + g c₃ + g c₄ + ∑ x ∈ B \ {c₀, c₁, c₂, c₃, c₄}, g x := by
  rw [← Finset.sum_sdiff A.five_subset, Finset.sum_insert (by simp [A.n01, A.n02, A.n03, A.n04]),
    Finset.sum_insert (by simp [A.n12, A.n13, A.n14]), Finset.sum_insert (by simp [A.n23, A.n24]),
    Finset.sum_pair A.n34]
  ring

theorem ShapeA.Θ_values (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) :
    Θ c₀ = δ₀ ∧ Θ c₁ = δ₁ ∧ Θ c₂ = δ₂ ∧ Θ c₃ = δ₃ ∧ Θ c₄ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [A.hΘ _ A.h₀]; simp [A.n01, A.n02, A.n03]
  · rw [A.hΘ _ A.h₁]; simp [A.n01.symm, A.n12, A.n13]
  · rw [A.hΘ _ A.h₂]; simp [A.n02.symm, A.n12.symm, A.n23]
  · rw [A.hΘ _ A.h₃]; simp [A.n03.symm, A.n13.symm, A.n23.symm]
  · rw [A.hΘ _ A.h₄]; simp [A.n04.symm, A.n14.symm, A.n24.symm, A.n34.symm]

theorem ShapeA.U_values (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) :
    U c₀ = δ₀ ∧ U c₁ = -δ₁ ∧ U c₂ = δ₂ ∧ U c₃ = -δ₃ ∧ U c₄ = 2 * δ₄ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [A.hU _ A.h₀]; simp [A.n01, A.n02, A.n03, A.n04]
  · rw [A.hU _ A.h₁]; simp [A.n01.symm, A.n12, A.n13, A.n14]
  · rw [A.hU _ A.h₂]; simp [A.n02.symm, A.n12.symm, A.n23, A.n24]
  · rw [A.hU _ A.h₃]; simp [A.n03.symm, A.n13.symm, A.n23.symm, A.n34]
  · rw [A.hU _ A.h₄]; simp [A.n04.symm, A.n14.symm, A.n24.symm, A.n34.symm]

theorem ShapeA.vanish (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) {x : L}
    (hx : x ∈ B \ {c₀, c₁, c₂, c₃, c₄}) : Θ x = 0 ∧ U x = 0 := by
  obtain ⟨hxB, h0, h1, h2, h3, h4⟩ := mem_sdiff_five.mp hx
  exact ⟨by rw [A.hΘ x hxB]; simp [h0, h1, h2, h3], by rw [A.hU x hxB]; simp [h0, h1, h2, h3, h4]⟩

end ShapeA

theorem theta_mul_self_le_one {B : Finset L} {deg Θ : L → ℤ} (hdeg : ∀ x ∈ B, 0 < deg x)
    (hΘΘ : ∑ x ∈ B, Θ x * Θ x = 4) (hdegΘ : ∑ x ∈ B, deg x * Θ x = 0) :
    ∀ x ∈ B, Θ x * Θ x ≤ 1 := by
  intro a ha
  by_contra hlt
  have hlt : 1 < Θ a * Θ a := not_le.mp hlt
  have h4 : 4 ≤ Θ a * Θ a := by
    rcases le_or_gt (Θ a) (-2) with h | h
    · nlinarith
    rcases le_or_gt 2 (Θ a) with h' | h'
    · nlinarith
    rcases (by omega : Θ a = -1 ∨ Θ a = 0 ∨ Θ a = 1) with h'' | h'' | h'' <;>
      rw [h''] at hlt <;> norm_num at hlt
  have hrest := eq_zero_of_le_mul_self ha hΘΘ h4
  have hsingle : ∑ x ∈ B, deg x * Θ x = deg a * Θ a :=
    Finset.sum_eq_single_of_mem a ha fun x hx hxa => by rw [hrest x hx hxa, mul_zero]
  rw [hsingle] at hdegΘ
  have hΘa : Θ a = 0 := (mul_eq_zero.mp hdegΘ).resolve_left (hdeg a ha).ne'
  rw [hΘa] at hlt
  norm_num at hlt

theorem stageA_support {B : Finset L} {deg Θ U : L → ℤ} (hdeg : ∀ x ∈ B, 0 < deg x)
    (hΘΘ : ∑ x ∈ B, Θ x * Θ x = 4) (hUU : ∑ x ∈ B, U x * U x = 8)
    (hdegΘ : ∑ x ∈ B, deg x * Θ x = 0) (hpar : ∀ x ∈ B, Even (U x + Θ x)) :
    #(B.filter fun x => Θ x ≠ 0) = 4 ∧
      (∀ x ∈ B, Θ x ≠ 0 → (Θ x = 1 ∨ Θ x = -1) ∧ (U x = 1 ∨ U x = -1)) ∧
      ∃ c₄ ∈ B, Θ c₄ = 0 ∧ ∃ δ₄ : ℤ, (δ₄ = 1 ∨ δ₄ = -1) ∧ U c₄ = 2 * δ₄ ∧
        ∀ x ∈ B, Θ x = 0 → x ≠ c₄ → U x = 0 := by
  have hΘ1 := theta_mul_self_le_one hdeg hΘΘ hdegΘ
  set S := B.filter fun x => Θ x ≠ 0 with hS
  have hScard : #S = 4 := by
    have := sum_mul_self_eq_card hΘ1
    rw [hΘΘ] at this
    exact_mod_cast this.symm
  have hSB : S ⊆ B := Finset.filter_subset _ _
  have hΘS : ∀ x ∈ B, Θ x ≠ 0 → Θ x = 1 ∨ Θ x = -1 := fun x hx h0 =>
    ((eq_zero_or_one_or_neg_one (hΘ1 x hx)).resolve_left h0)
  have hUodd : ∀ x ∈ S, Odd (U x) := by
    intro x hx
    obtain ⟨hxB, hx0⟩ := Finset.mem_filter.mp hx
    have e := hpar x hxB
    rw [Int.even_iff] at e
    rw [Int.odd_iff]
    rcases hΘS x hxB hx0 with h | h <;> rw [h] at e <;> omega
  have hUeven : ∀ x ∈ B \ S, Even (U x) := by
    intro x hx
    obtain ⟨hxB, hxS⟩ := Finset.mem_sdiff.mp hx
    have hΘx : Θ x = 0 := by
      by_contra h
      exact hxS (Finset.mem_filter.mpr ⟨hxB, h⟩)
    simpa [hΘx] using hpar x hxB
  have hsplit := Finset.sum_sdiff hSB (f := fun x => U x * U x)
  have hSge : ∀ x ∈ S, 1 ≤ U x * U x := fun x hx =>
    one_le_mul_self_of_ne_zero fun h => by simpa [h] using hUodd x hx
  have hRnn : 0 ≤ ∑ x ∈ B \ S, U x * U x := Finset.sum_nonneg fun x _ => mul_self_nonneg _
  have hUS : ∀ x ∈ S, U x = 1 ∨ U x = -1 := by
    intro a ha
    have herase := Finset.add_sum_erase S (fun x => U x * U x) ha
    have h3 : (3 : ℤ) ≤ ∑ x ∈ S.erase a, U x * U x := by
      have := Finset.card_nsmul_le_sum (S.erase a) (fun x => U x * U x) 1
        (fun x hx => hSge x (Finset.mem_of_mem_erase hx))
      rw [Finset.card_erase_of_mem ha, hScard] at this
      simpa using this
    exact eq_one_or_neg_one_of_odd (hUodd a ha) (by linarith)
  have hSsum : ∑ x ∈ S, U x * U x = 4 := by
    rw [Finset.sum_congr rfl fun x hx => (show U x * U x = 1 by
      rcases hUS x hx with h | h <;> rw [h] <;> norm_num)]
    simp [hScard]
  have hR : ∑ x ∈ B \ S, U x * U x = 4 := by linarith
  obtain ⟨c₄, hc₄R, hc₄sq, hc₄rest⟩ := exists_unique_ne_zero (by norm_num) hR
    (fun x hx hne => four_le_mul_self_of_even (hUeven x hx) hne)
  obtain ⟨hc₄B, hc₄S⟩ := Finset.mem_sdiff.mp hc₄R
  have hΘc₄ : Θ c₄ = 0 := by
    by_contra h
    exact hc₄S (Finset.mem_filter.mpr ⟨hc₄B, h⟩)
  obtain ⟨m, hm⟩ := hUeven c₄ hc₄R
  have hmm : m * m = 1 := by
    rw [hm] at hc₄sq
    nlinarith
  refine ⟨hScard, fun x hx h0 => ⟨hΘS x hx h0, hUS x (Finset.mem_filter.mpr ⟨hx, h0⟩)⟩, c₄, hc₄B,
    hΘc₄, m, mul_self_eq_one_iff.mp hmm, by rw [hm]; ring, fun x hx hΘx hxc => ?_⟩
  refine hc₄rest x (Finset.mem_sdiff.mpr ⟨hx, fun hxS => ?_⟩) hxc
  exact (Finset.mem_filter.mp hxS).2 hΘx

theorem stageA {B : Finset L} {deg Θ U : L → ℤ} (hdeg : ∀ x ∈ B, 0 < deg x)
    (hΘΘ : ∑ x ∈ B, Θ x * Θ x = 4) (hUU : ∑ x ∈ B, U x * U x = 8)
    (hUΘ : ∑ x ∈ B, U x * Θ x = 0) (hdegΘ : ∑ x ∈ B, deg x * Θ x = 0)
    (hpar : ∀ x ∈ B, Even (U x + Θ x)) :
    ∃ (c₀ c₁ c₂ c₃ c₄ : L) (δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ), ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄ := by
  obtain ⟨hScard, hval, c₄, hc₄B, hΘc₄, δ₄, hδ₄, hUc₄, hU0⟩ :=
    stageA_support hdeg hΘΘ hUU hdegΘ hpar
  set S := B.filter fun x => Θ x ≠ 0 with hS
  have hSB : S ⊆ B := Finset.filter_subset _ _
  have hmemS : ∀ x, x ∈ S ↔ x ∈ B ∧ Θ x ≠ 0 := fun x => Finset.mem_filter
  have hp : ∀ x ∈ S, U x * Θ x = 1 ∨ U x * Θ x = -1 := by
    intro x hx
    obtain ⟨hxB, hx0⟩ := (hmemS x).mp hx
    obtain ⟨h1, h2⟩ := hval x hxB hx0
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have hpsum : ∑ x ∈ S, U x * Θ x = 0 := by
    rw [← hUΘ]
    refine Finset.sum_subset hSB fun x hxB hxS => ?_
    have : Θ x = 0 := by
      by_contra h
      exact hxS ((hmemS x).mpr ⟨hxB, h⟩)
    rw [this, mul_zero]
  obtain ⟨hP2, hN2⟩ := card_filter_eq_one_of_sum_eq_zero hp hpsum
  rw [hScard] at hP2 hN2
  obtain ⟨c₀, c₂, h02, hP⟩ :=
    Finset.card_eq_two.mp (by omega : #(S.filter fun x => U x * Θ x = 1) = 2)
  obtain ⟨c₁, c₃, h13, hN⟩ :=
    Finset.card_eq_two.mp (by omega : #(S.filter fun x => ¬U x * Θ x = 1) = 2)
  have hc₀ : c₀ ∈ S ∧ U c₀ * Θ c₀ = 1 := Finset.mem_filter.mp
    (show c₀ ∈ S.filter fun x => U x * Θ x = 1 by rw [hP]; simp)
  have hc₂ : c₂ ∈ S ∧ U c₂ * Θ c₂ = 1 := Finset.mem_filter.mp
    (show c₂ ∈ S.filter fun x => U x * Θ x = 1 by rw [hP]; simp)
  have hc₁ : c₁ ∈ S ∧ ¬U c₁ * Θ c₁ = 1 := Finset.mem_filter.mp
    (show c₁ ∈ S.filter fun x => ¬U x * Θ x = 1 by rw [hN]; simp)
  have hc₃ : c₃ ∈ S ∧ ¬U c₃ * Θ c₃ = 1 := Finset.mem_filter.mp
    (show c₃ ∈ S.filter fun x => ¬U x * Θ x = 1 by rw [hN]; simp)
  have hcases : ∀ x ∈ S, x = c₀ ∨ x = c₁ ∨ x = c₂ ∨ x = c₃ := by
    intro x hx
    by_cases h : U x * Θ x = 1
    · have : x ∈ S.filter fun x => U x * Θ x = 1 := Finset.mem_filter.mpr ⟨hx, h⟩
      rw [hP] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
    · have : x ∈ S.filter fun x => ¬U x * Θ x = 1 := Finset.mem_filter.mpr ⟨hx, h⟩
      rw [hN] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
  have hB : ∀ x ∈ S, x ∈ B := fun x hx => hSB hx
  have hne4 : ∀ x ∈ S, x ≠ c₄ := fun x hx e => ((hmemS x).mp hx).2 (e ▸ hΘc₄)
  have hsign : ∀ x ∈ S, Θ x = 1 ∨ Θ x = -1 := fun x hx =>
    (hval x ((hmemS x).mp hx).1 ((hmemS x).mp hx).2).1
  have hUplus : ∀ x ∈ S, U x * Θ x = 1 → U x = Θ x := by
    intro x hx h
    rcases hsign x hx with e | e <;> rw [e] at h ⊢ <;> linarith
  have hUminus : ∀ x ∈ S, ¬U x * Θ x = 1 → U x = -Θ x := by
    intro x hx h
    have h' := (hp x hx).resolve_left h
    rcases hsign x hx with e | e <;> rw [e] at h' ⊢ <;> linarith
  have n01 : c₀ ≠ c₁ := fun e => hc₁.2 (e ▸ hc₀.2)
  have n03 : c₀ ≠ c₃ := fun e => hc₃.2 (e ▸ hc₀.2)
  have n12 : c₁ ≠ c₂ := fun e => hc₁.2 (e ▸ hc₂.2)
  have n23 : c₂ ≠ c₃ := fun e => hc₃.2 (e ▸ hc₂.2)
  have hU₀ := hUplus c₀ hc₀.1 hc₀.2
  have hU₂ := hUplus c₂ hc₂.1 hc₂.2
  have hU₁ := hUminus c₁ hc₁.1 hc₁.2
  have hU₃ := hUminus c₃ hc₃.1 hc₃.2
  refine ⟨c₀, c₁, c₂, c₃, c₄, Θ c₀, Θ c₁, Θ c₂, Θ c₃, δ₄,
    { h₀ := hB c₀ hc₀.1, h₁ := hB c₁ hc₁.1, h₂ := hB c₂ hc₂.1, h₃ := hB c₃ hc₃.1, h₄ := hc₄B,
      n01 := n01, n02 := h02, n03 := n03, n04 := hne4 c₀ hc₀.1, n12 := n12, n13 := h13,
      n14 := hne4 c₁ hc₁.1, n23 := n23, n24 := hne4 c₂ hc₂.1, n34 := hne4 c₃ hc₃.1,
      s₀ := hsign c₀ hc₀.1, s₁ := hsign c₁ hc₁.1, s₂ := hsign c₂ hc₂.1, s₃ := hsign c₃ hc₃.1,
      s₄ := hδ₄, hΘ := ?_, hU := ?_ }⟩
  · intro x hx
    by_cases hx0 : Θ x = 0
    · have hxS : x ∉ S := fun h => ((hmemS x).mp h).2 hx0
      have e0 : x ≠ c₀ := fun e => hxS (e ▸ hc₀.1)
      have e1 : x ≠ c₁ := fun e => hxS (e ▸ hc₁.1)
      have e2 : x ≠ c₂ := fun e => hxS (e ▸ hc₂.1)
      have e3 : x ≠ c₃ := fun e => hxS (e ▸ hc₃.1)
      simp [hx0, e0, e1, e2, e3]
    · rcases hcases x ((hmemS x).mpr ⟨hx, hx0⟩) with rfl | rfl | rfl | rfl
      · simp [n01, h02, n03]
      · simp [n01.symm, n12, h13]
      · simp [h02.symm, n12.symm, n23]
      · simp [n03.symm, h13.symm, n23.symm]
  · intro x hx
    by_cases hx0 : Θ x = 0
    · have hxS : x ∉ S := fun h => ((hmemS x).mp h).2 hx0
      have e0 : x ≠ c₀ := fun e => hxS (e ▸ hc₀.1)
      have e1 : x ≠ c₁ := fun e => hxS (e ▸ hc₁.1)
      have e2 : x ≠ c₂ := fun e => hxS (e ▸ hc₂.1)
      have e3 : x ≠ c₃ := fun e => hxS (e ▸ hc₃.1)
      by_cases e4 : x = c₄
      · subst e4
        simp [e0, e1, e2, e3, hUc₄]
      · simp [e0, e1, e2, e3, e4, hU0 x hx hx0 e4]
    · have hxS := (hmemS x).mpr ⟨hx, hx0⟩
      have e4 := hne4 x hxS
      rcases hcases x hxS with rfl | rfl | rfl | rfl
      · simp [n01, h02, n03, e4, hU₀]
      · simp [n01.symm, n12, h13, e4, hU₁]
      · simp [h02.symm, n12.symm, n23, e4, hU₂]
      · simp [n03.symm, h13.symm, n23.symm, e4, hU₃]

structure ShapeE (B : Finset L) (c₀ c₁ c₂ c₃ c₄ : L) (δ₀ δ₁ δ₂ δ₃ : ℤ) (E : L → ℤ) (a b : ℤ)
    (p : L) (s : ℤ) : Prop where
  ha : a = 0 ∨ a = 1
  hb : b = 0 ∨ b = 1
  hp : p ∈ B \ {c₀, c₁, c₂, c₃, c₄}
  hs : s = 1 ∨ s = -1
  e₀ : E c₀ = δ₀ * a
  e₁ : E c₁ = δ₁ * b
  e₂ : E c₂ = δ₂ * (1 - a)
  e₃ : E c₃ = δ₃ * (1 - b)
  e₄ : E c₄ = 0
  ep : E p = s
  eout : ∀ x ∈ B \ {c₀, c₁, c₂, c₃, c₄}, x ≠ p → E x = 0

theorem stageB_arith {u₀ u₁ u₂ u₃ u₄ : ℤ} (b0 : u₀ * u₀ ≤ 1) (b1 : u₁ * u₁ ≤ 1)
    (b2 : u₂ * u₂ ≤ 1) (b3 : u₃ * u₃ ≤ 1) (b4 : u₄ * u₄ ≤ 1)
    (h1 : u₀ + u₁ + u₂ + u₃ = 2) (h2 : u₀ - u₁ + u₂ - u₃ + 2 * u₄ = 0) :
    (u₄ = 1 ∧ u₁ = 1 ∧ u₃ = 1) ∨ (u₄ = -1 ∧ u₀ = 1 ∧ u₂ = 1) ∨
      (u₄ = 0 ∧ ((u₀ = 1 ∧ u₂ = 0) ∨ (u₀ = 0 ∧ u₂ = 1)) ∧
        ((u₁ = 1 ∧ u₃ = 0) ∨ (u₁ = 0 ∧ u₃ = 1))) := by
  have l0 : -1 ≤ u₀ ∧ u₀ ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have l1 : -1 ≤ u₁ ∧ u₁ ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have l2 : -1 ≤ u₂ ∧ u₂ ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have l3 : -1 ≤ u₃ ∧ u₃ ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  rcases eq_zero_or_one_or_neg_one b4 with h4 | h4 | h4
  · right; right
    refine ⟨h4, ?_, ?_⟩
    · rcases eq_zero_or_one_or_neg_one b0 with h | h | h
      · right; omega
      · left; omega
      · omega
    · rcases eq_zero_or_one_or_neg_one b1 with h | h | h
      · right; omega
      · left; omega
      · omega
  · left; omega
  · right; left; omega

section StageB

variable {B : Finset L} {Θ U : L → ℤ} {c₀ c₁ c₂ c₃ c₄ : L} {δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ}

theorem eq_sign_mul_of_sign_mul_eq {δ e u : ℤ} (hδ : δ = 1 ∨ δ = -1) (h : δ * e = u) :
    e = δ * u := by
  rw [← h, ← mul_assoc, sign_mul_self hδ, one_mul]

theorem stageB (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) {deg E : L → ℤ}
    (hdeg : ∀ x ∈ B, 0 < deg x) (hdegΘ : ∑ x ∈ B, deg x * Θ x = 0)
    (hdegU : ∑ x ∈ B, deg x * U x = 0) (hEE : ∑ x ∈ B, E x * E x = 3)
    (hΘE : ∑ x ∈ B, Θ x * E x = 2) (hUE : ∑ x ∈ B, U x * E x = 0)
    (hdegE : ∑ x ∈ B, deg x * E x = 0) :
    ∃ (a b : ℤ) (p : L) (s : ℤ), ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ E a b p s := by
  have hE1 : ∀ x ∈ B, E x * E x ≤ 1 := fun x hx => mul_self_le_one_of_lt_four (by
    have := Finset.single_le_sum (f := fun x => E x * E x) (fun x _ => mul_self_nonneg _) hx
    omega)
  rw [A.sum_Θ_mul E] at hΘE
  rw [A.sum_U_mul E] at hUE
  rw [A.sum_mul_Θ deg] at hdegΘ
  rw [A.sum_mul_U deg] at hdegU
  rw [A.sum_split] at hEE hdegE
  set R := ∑ x ∈ B \ {c₀, c₁, c₂, c₃, c₄}, E x * E x with hR
  set R' := ∑ x ∈ B \ {c₀, c₁, c₂, c₃, c₄}, deg x * E x with hR'
  have hRnn : 0 ≤ R := Finset.sum_nonneg fun x _ => mul_self_nonneg _
  have hR0 : R = 0 → ∀ x ∈ B \ {c₀, c₁, c₂, c₃, c₄}, E x = 0 := by
    intro h x hx
    exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      fun y _ => mul_self_nonneg (E y)).mp h x hx)
  have hR'0 : R = 0 → R' = 0 := fun h =>
    Finset.sum_eq_zero fun x hx => by rw [hR0 h x hx, mul_zero]
  have hsq : ∀ {δ : ℤ}, (δ = 1 ∨ δ = -1) → ∀ e : ℤ, (δ * e) * (δ * e) = e * e := by
    intro δ hδ e
    rw [show δ * e * (δ * e) = (δ * δ) * (e * e) by ring, sign_mul_self hδ, one_mul]
  have hb : ∀ {δ : ℤ}, (δ = 1 ∨ δ = -1) → ∀ x ∈ B, (δ * E x) * (δ * E x) ≤ 1 :=
    fun hδ x hx => by rw [hsq hδ]; exact hE1 x hx
  have e₀ := eq_sign_mul_of_sign_mul_eq A.s₀ (rfl : δ₀ * E c₀ = _)
  have e₁ := eq_sign_mul_of_sign_mul_eq A.s₁ (rfl : δ₁ * E c₁ = _)
  have e₂ := eq_sign_mul_of_sign_mul_eq A.s₂ (rfl : δ₂ * E c₂ = _)
  have e₃ := eq_sign_mul_of_sign_mul_eq A.s₃ (rfl : δ₃ * E c₃ = _)
  have e₄ := eq_sign_mul_of_sign_mul_eq A.s₄ (rfl : δ₄ * E c₄ = _)
  have hEE' : (δ₀ * E c₀) * (δ₀ * E c₀) + (δ₁ * E c₁) * (δ₁ * E c₁) +
      (δ₂ * E c₂) * (δ₂ * E c₂) + (δ₃ * E c₃) * (δ₃ * E c₃) + (δ₄ * E c₄) * (δ₄ * E c₄) + R =
      3 := by
    rw [hsq A.s₀, hsq A.s₁, hsq A.s₂, hsq A.s₃, hsq A.s₄]
    exact hEE
  have hd4 := hdeg c₄ A.h₄
  rcases stageB_arith (hb A.s₀ c₀ A.h₀) (hb A.s₁ c₁ A.h₁) (hb A.s₂ c₂ A.h₂) (hb A.s₃ c₃ A.h₃)
      (hb A.s₄ c₄ A.h₄) (by linear_combination hΘE) (by linear_combination hUE) with
    ⟨u4, u1, u3⟩ | ⟨u4, u0, u2⟩ | ⟨u4, h02, h13⟩
  · exfalso
    rw [u1, u3, u4] at hEE'
    have hn0 := mul_self_nonneg (δ₀ * E c₀)
    have hn2 := mul_self_nonneg (δ₂ * E c₂)
    have hR00 : R = 0 := by linarith
    have z0 : δ₀ * E c₀ = 0 := mul_self_eq_zero.mp (by linarith)
    have z2 : δ₂ * E c₂ = 0 := mul_self_eq_zero.mp (by linarith)
    rw [z0, mul_zero] at e₀
    rw [z2, mul_zero] at e₂
    rw [u1, mul_one] at e₁
    rw [u3, mul_one] at e₃
    rw [u4, mul_one] at e₄
    rw [e₀, e₁, e₂, e₃, e₄, hR'0 hR00] at hdegE
    have key : 4 * (δ₄ * deg c₄) = 0 := by linear_combination -hdegΘ + hdegU + 2 * hdegE
    rcases A.s₄ with h | h <;> rw [h] at key <;> linarith
  · exfalso
    rw [u0, u2, u4] at hEE'
    have hn1 := mul_self_nonneg (δ₁ * E c₁)
    have hn3 := mul_self_nonneg (δ₃ * E c₃)
    have hR00 : R = 0 := by linarith
    have z1 : δ₁ * E c₁ = 0 := mul_self_eq_zero.mp (by linarith)
    have z3 : δ₃ * E c₃ = 0 := mul_self_eq_zero.mp (by linarith)
    rw [z1, mul_zero] at e₁
    rw [z3, mul_zero] at e₃
    rw [u0, mul_one] at e₀
    rw [u2, mul_one] at e₂
    rw [u4] at e₄
    rw [e₀, e₁, e₂, e₃, e₄, hR'0 hR00] at hdegE
    have key : 4 * (δ₄ * deg c₄) = 0 := by linear_combination hdegΘ + hdegU - 2 * hdegE
    rcases A.s₄ with h | h <;> rw [h] at key <;> linarith
  · have hR1 : R = 1 := by
      rw [u4] at hEE'
      rcases h02 with ⟨h0, h2⟩ | ⟨h0, h2⟩ <;> rcases h13 with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;>
        rw [h0, h1, h2, h3] at hEE' <;> linarith
    obtain ⟨p, hp, hpsq, hrest⟩ := exists_unique_ne_zero (by norm_num) hR1
      (fun x _ hne => one_le_mul_self_of_ne_zero hne)
    refine ⟨δ₀ * E c₀, δ₁ * E c₁, p, E p, ?_⟩
    exact {
      ha := by rcases h02 with ⟨h0, -⟩ | ⟨h0, -⟩ <;> rw [h0] <;> simp
      hb := by rcases h13 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp
      hp := hp
      hs := mul_self_eq_one_iff.mp hpsq
      e₀ := e₀
      e₁ := e₁
      e₂ := by
        rw [e₂]
        congr 1
        rcases h02 with ⟨h0, h2⟩ | ⟨h0, h2⟩ <;> rw [h0, h2] <;> norm_num
      e₃ := by
        rw [e₃]
        congr 1
        rcases h13 with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;> rw [h1, h3] <;> norm_num
      e₄ := by rw [e₄, u4, mul_zero]
      ep := rfl
      eout := hrest }

end StageB

end TableCoordinates

end CFSG.Semidihedral.FieldFactorOne
