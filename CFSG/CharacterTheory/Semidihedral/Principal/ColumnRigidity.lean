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

namespace CFSG.Semidihedral.Principal

open Finset

variable {ι : Type*} [DecidableEq ι]

namespace ColumnRigidity

theorem one_le_mul_self_of_odd {u : ℤ} (hu : Odd u) : 1 ≤ u * u := by
  have hne : u ≠ 0 := by
    rintro rfl
    simp at hu
  have := mul_self_pos.mpr hne
  omega

theorem eq_one_or_neg_one_of_odd {u : ℤ} (hu : Odd u) (h : u * u < 9) : u = 1 ∨ u = -1 := by
  obtain ⟨m, rfl⟩ := hu
  have h1 : -2 < m := by nlinarith
  have h2 : m < 1 := by nlinarith
  omega

theorem sign_mul_self {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) : δ * δ = 1 := by
  rcases hδ with rfl | rfl <;> norm_num

theorem sign_ne_zero {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) : δ ≠ 0 := by
  rcases hδ with rfl | rfl <;> norm_num

theorem norm_eight_shape {B : Finset ι} {U : ι → ℤ} {x₀ x₁ x₂ x₃ : ι}
    (hx₀ : x₀ ∈ B) (hx₁ : x₁ ∈ B) (hx₂ : x₂ ∈ B) (hx₃ : x₃ ∈ B)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h23 : x₂ ≠ x₃) (hU₀ : U x₀ = 1) (hU₁ : Odd (U x₁)) (hU₂ : Odd (U x₂)) (hU₃ : Odd (U x₃))
    (heven : ∀ y ∈ B, y ≠ x₀ → y ≠ x₁ → y ≠ x₂ → y ≠ x₃ → Even (U y))
    (hUU : ∑ y ∈ B, U y * U y = 8) :
    (U x₁ = 1 ∨ U x₁ = -1) ∧ (U x₂ = 1 ∨ U x₂ = -1) ∧ (U x₃ = 1 ∨ U x₃ = -1) ∧
    ∃ x₄ ∈ B, x₄ ≠ x₀ ∧ x₄ ≠ x₁ ∧ x₄ ≠ x₂ ∧ x₄ ≠ x₃ ∧
      ∃ δ₄ : ℤ, (δ₄ = 1 ∨ δ₄ = -1) ∧ U x₄ = 2 * δ₄ ∧
        ∀ y ∈ B, y ≠ x₀ → y ≠ x₁ → y ≠ x₂ → y ≠ x₃ → y ≠ x₄ → U y = 0 := by
  set S : Finset ι := {x₀, x₁, x₂, x₃} with hS
  have hSB : S ⊆ B := by
    intro y hy
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> assumption
  have hsplit := Finset.sum_sdiff hSB (f := fun y => U y * U y)
  have hSsum : ∑ y ∈ S, U y * U y = U x₀ * U x₀ + U x₁ * U x₁ + U x₂ * U x₂ + U x₃ * U x₃ := by
    rw [hS, Finset.sum_insert (by simp [h01, h02, h03]), Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_pair h23]
    ring
  have hmemR : ∀ y ∈ B \ S, y ∈ B ∧ y ≠ x₀ ∧ y ≠ x₁ ∧ y ≠ x₂ ∧ y ≠ x₃ := by
    intro y hy
    simp only [Finset.mem_sdiff, hS, Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    exact ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2⟩
  have hRnn : 0 ≤ ∑ y ∈ B \ S, U y * U y := Finset.sum_nonneg fun y _ => mul_self_nonneg _
  have htot : 1 + U x₁ * U x₁ + U x₂ * U x₂ + U x₃ * U x₃ + ∑ y ∈ B \ S, U y * U y = 8 := by
    rw [hU₀] at hSsum
    linarith
  have hs₁ := one_le_mul_self_of_odd hU₁
  have hs₂ := one_le_mul_self_of_odd hU₂
  have hs₃ := one_le_mul_self_of_odd hU₃
  have hv₁ := eq_one_or_neg_one_of_odd hU₁ (by linarith)
  have hv₂ := eq_one_or_neg_one_of_odd hU₂ (by linarith)
  have hv₃ := eq_one_or_neg_one_of_odd hU₃ (by linarith)
  have hR4 : ∑ y ∈ B \ S, U y * U y = 4 := by
    have e₁ := sign_mul_self hv₁
    have e₂ := sign_mul_self hv₂
    have e₃ := sign_mul_self hv₃
    linarith
  obtain ⟨x₄, hx₄R, hx₄ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hR4]; norm_num)
  obtain ⟨hx₄B, h40, h41, h42, h43⟩ := hmemR x₄ hx₄R
  obtain ⟨m, hm⟩ := heven x₄ hx₄B h40 h41 h42 h43
  have herase := Finset.add_sum_erase (B \ S) (fun y => U y * U y) hx₄R
  have hrest : 0 ≤ ∑ y ∈ (B \ S).erase x₄, U y * U y :=
    Finset.sum_nonneg fun y _ => mul_self_nonneg _
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hx₄ne (by simp [hm])
  have hmm : m * m = 1 := by
    have hle : U x₄ * U x₄ ≤ 4 := by linarith
    rw [hm] at hle
    have : 1 ≤ m * m := by
      rcases lt_or_gt_of_ne hm0 with h | h <;> nlinarith
    nlinarith
  have hrest0 : ∑ y ∈ (B \ S).erase x₄, U y * U y = 0 := by
    rw [hm] at herase
    nlinarith
  refine ⟨hv₁, hv₂, hv₃, x₄, hx₄B, h40, h41, h42, h43, m, mul_self_eq_one_iff.mp hmm,
    by rw [hm]; ring, ?_⟩
  intro y hy hy0 hy1 hy2 hy3 hy4
  have hmem : y ∈ (B \ S).erase x₄ := by
    simp only [Finset.mem_erase, Finset.mem_sdiff, hS, Finset.mem_insert, Finset.mem_singleton,
      not_or]
    exact ⟨hy4, hy, hy0, hy1, hy2, hy3⟩
  exact mul_self_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun y _ => mul_self_nonneg (U y)).mp hrest0 y hmem)

theorem odd_support_of_norm_eq_card {B D : Finset ι} {V : ι → ℤ} (hDB : D ⊆ B)
    (hodd : ∀ y ∈ D, Odd (V y)) (hVV : ∑ y ∈ B, V y * V y = #D) :
    (∀ y ∈ D, V y = 1 ∨ V y = -1) ∧ ∀ y ∈ B, y ∉ D → V y = 0 := by
  have hsplit := Finset.sum_sdiff hDB (f := fun y => V y * V y)
  have hge : ∀ y ∈ D, 1 ≤ V y * V y := fun y hy => one_le_mul_self_of_odd (hodd y hy)
  have hD : (#D : ℤ) ≤ ∑ y ∈ D, V y * V y := by
    have := Finset.card_nsmul_le_sum D (fun y => V y * V y) 1 hge
    simpa using this
  have hnn : ∀ y ∈ B \ D, 0 ≤ V y * V y := fun y _ => mul_self_nonneg _
  have hR : ∑ y ∈ B \ D, V y * V y = 0 := by
    have := Finset.sum_nonneg hnn
    linarith
  have hDeq : ∑ y ∈ D, (V y * V y - 1) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  refine ⟨fun y hy => ?_, fun y hy hyD => ?_⟩
  · have h := (Finset.sum_eq_zero_iff_of_nonneg fun z hz => sub_nonneg.mpr (hge z hz)).mp hDeq
      y hy
    exact mul_self_eq_one_iff.mp (by linarith)
  · exact mul_self_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hR y (Finset.mem_sdiff.mpr ⟨hy, hyD⟩))

theorem sum_mul_single {B : Finset ι} (f : ι → ℤ) {x : ι} (hx : x ∈ B) :
    ∑ y ∈ B, f y * (Pi.single x 1 : ι → ℤ) y = f x := by
  simp [Pi.single_apply, hx]

theorem sum_single_mul {B : Finset ι} (f : ι → ℤ) {x : ι} (hx : x ∈ B) :
    ∑ y ∈ B, (Pi.single x 1 : ι → ℤ) y * f y = f x := by
  simp [Pi.single_apply, hx]

theorem sum_sum_single_mul {B : Finset ι} (f : ι → ℤ) {s : Finset ℕ} {a : ℕ → ι}
    (ha : ∀ j ∈ s, a j ∈ B) :
    ∑ y ∈ B, (∑ j ∈ s, (Pi.single (a j) 1 : ι → ℤ)) y * f y = ∑ j ∈ s, f (a j) := by
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j hj => sum_single_mul f (ha j hj)

theorem sum_single_apply_of_forall_ne {s : Finset ℕ} {a : ℕ → ι} {y : ι}
    (h : ∀ j ∈ s, y ≠ a j) : (∑ j ∈ s, (Pi.single (a j) 1 : ι → ℤ)) y = 0 := by
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero fun j hj => by simp [h j hj]

theorem sum_single_apply_of_injOn {s : Finset ℕ} {a : ℕ → ι} (ha : Set.InjOn a s) {j₀ : ℕ}
    (hj₀ : j₀ ∈ s) : (∑ j ∈ s, (Pi.single (a j) 1 : ι → ℤ)) (a j₀) = 1 := by
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem j₀ hj₀]
  · simp
  · intro j hj hne
    have : a j₀ ≠ a j := fun h => hne (ha hj hj₀ h.symm)
    simp [this]

theorem sum_mul_four {B : Finset ι} (f : ι → ℤ) {x₀ x₁ x₂ x₃ : ι} (hx₀ : x₀ ∈ B)
    (hx₁ : x₁ ∈ B) (hx₂ : x₂ ∈ B) (hx₃ : x₃ ∈ B) (δ₁ δ₂ δ₃ : ℤ) :
    ∑ y ∈ B, f y * (Pi.single x₀ 1 + δ₁ • Pi.single x₁ 1 + δ₂ • Pi.single x₂ 1 +
      δ₃ • Pi.single x₃ 1 : ι → ℤ) y = f x₀ + δ₁ * f x₁ + δ₂ * f x₂ + δ₃ * f x₃ := by
  simp [Pi.single_apply, hx₀, hx₁, hx₂, hx₃, mul_add, Finset.sum_add_distrib]
  ring

theorem sum_mul_three {B : Finset ι} (f : ι → ℤ) {x₀ x₁ z : ι} (hx₀ : x₀ ∈ B) (hx₁ : x₁ ∈ B)
    (hz : z ∈ B) (δ : ℤ) :
    ∑ y ∈ B, f y * (Pi.single x₀ 1 + δ • Pi.single x₁ 1 - δ • Pi.single z 1 : ι → ℤ) y =
      f x₀ + δ * f x₁ - δ * f z := by
  simp [Pi.single_apply, hx₀, hx₁, hz, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

theorem sum_mul_two {B : Finset ι} (f : ι → ℤ) {z w : ι} (hz : z ∈ B) (hw : w ∈ B) (ε : ℤ) :
    ∑ y ∈ B, f y * (ε • (Pi.single z 1 - Pi.single w 1) : ι → ℤ) y = ε * (f z - f w) := by
  simp [Pi.single_apply, hz, hw, mul_sub, Finset.sum_sub_distrib]
  ring

theorem sum_eq_five {B : Finset ι} (g : ι → ℤ) {x₀ x₁ x₂ x₃ x₄ : ι} (hx₀ : x₀ ∈ B)
    (hx₁ : x₁ ∈ B) (hx₂ : x₂ ∈ B) (hx₃ : x₃ ∈ B) (hx₄ : x₄ ∈ B) (h01 : x₀ ≠ x₁)
    (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃) (h04 : x₀ ≠ x₄) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h14 : x₁ ≠ x₄) (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄)
    (hg : ∀ y ∈ B, y ≠ x₀ → y ≠ x₁ → y ≠ x₂ → y ≠ x₃ → y ≠ x₄ → g y = 0) :
    ∑ y ∈ B, g y = g x₀ + g x₁ + g x₂ + g x₃ + g x₄ := by
  have hsub : ({x₀, x₁, x₂, x₃, x₄} : Finset ι) ⊆ B := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
  rw [← Finset.sum_subset hsub fun y hy hy' => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy'
    exact hg y hy hy'.1 hy'.2.1 hy'.2.2.1 hy'.2.2.2.1 hy'.2.2.2.2]
  rw [Finset.sum_insert (by simp [h01, h02, h03, h04]),
    Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
    Finset.sum_pair h34]
  ring

theorem sum_five_part_mul {B : Finset ι} (f : ι → ℤ) {x₁ x₂ x₄ : ι} (hx₁ : x₁ ∈ B)
    (hx₂ : x₂ ∈ B) (hx₄ : x₄ ∈ B) {s t : Finset ℕ} {a b : ℕ → ι} (ha : ∀ j ∈ s, a j ∈ B)
    (hb : ∀ i ∈ t, b i ∈ B) (c₁ c₂ c₄ cₐ c_b : ℤ) :
    ∑ y ∈ B, (c₁ • Pi.single x₁ 1 - c₂ • Pi.single x₂ 1 - c₄ • Pi.single x₄ 1 +
        cₐ • ∑ j ∈ s, Pi.single (a j) 1 - c_b • ∑ i ∈ t, Pi.single (b i) 1 : ι → ℤ) y * f y =
      c₁ * f x₁ - c₂ * f x₂ - c₄ * f x₄ + cₐ * ∑ j ∈ s, f (a j) - c_b * ∑ i ∈ t, f (b i) := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [sum_single_mul f hx₁, sum_single_mul f hx₂, sum_single_mul f hx₄, sum_sum_single_mul f ha,
    sum_sum_single_mul f hb]

structure Hyp (B : Finset ι) (k : ℕ) (d : ι → ℤ) (x₀ x₁ x₂ x₃ : ι) (a b : ℕ → ι)
    (δ₁ δ₂ δ₃ ε : ℤ) (T : ι → ℤ) (P F : ℕ → ι → ℤ) (U V : ι → ℤ) : Prop where
  hk : 2 ≤ k
  hk_even : Even k
  hd : ∀ y ∈ B, 0 < d y
  hx₀ : x₀ ∈ B
  hx₁ : x₁ ∈ B
  hx₂ : x₂ ∈ B
  hx₃ : x₃ ∈ B
  h01 : x₀ ≠ x₁
  h02 : x₀ ≠ x₂
  h03 : x₀ ≠ x₃
  h12 : x₁ ≠ x₂
  h13 : x₁ ≠ x₃
  h23 : x₂ ≠ x₃
  hdx₀ : d x₀ = 1
  ha : ∀ j ∈ Icc 1 (k - 1), a j ∈ B
  ha_inj : Set.InjOn a (Icc 1 (k - 1))
  ha_x : ∀ j ∈ Icc 1 (k - 1), a j ≠ x₀ ∧ a j ≠ x₁ ∧ a j ≠ x₂ ∧ a j ≠ x₃
  hb : ∀ i ∈ range k, b i ∈ B
  hb_inj : Set.InjOn b (range k)
  hb_x : ∀ i ∈ range k, b i ≠ x₀ ∧ b i ≠ x₁
  hb_a : ∀ i ∈ range k, ∀ j ∈ Icc 1 (k - 1), b i ≠ a j
  hδ₁ : δ₁ = 1 ∨ δ₁ = -1
  hδ₂ : δ₂ = 1 ∨ δ₂ = -1
  hδ₃ : δ₃ = 1 ∨ δ₃ = -1
  hε : ε = 1 ∨ ε = -1
  hT : T = Pi.single x₀ 1 + δ₁ • Pi.single x₁ 1 + δ₂ • Pi.single x₂ 1 + δ₃ • Pi.single x₃ 1
  hP : ∀ j ∈ Icc 1 (k - 1),
    P j = Pi.single x₀ 1 + δ₁ • Pi.single x₁ 1 - δ₁ • Pi.single (a j) 1
  hF : ∀ i ∈ range k, F i = ε • (Pi.single (b i) 1 - Pi.single (b 0) 1)
  hdT : ∑ y ∈ B, d y * T y = 0
  hdP : ∀ j ∈ Icc 1 (k - 1), ∑ y ∈ B, d y * P j y = 0
  hdF : ∀ i ∈ range k, ∑ y ∈ B, d y * F i y = 0
  hTF : ∀ i ∈ range k, ∑ y ∈ B, T y * F i y = 0
  hPF : ∀ j ∈ Icc 1 (k - 1), ∀ i ∈ range k, ∑ y ∈ B, P j y * F i y = 0
  hUd : ∑ y ∈ B, U y * d y = 0
  hUT : ∑ y ∈ B, U y * T y = 0
  hUP : ∀ j ∈ Icc 1 (k - 1), ∑ y ∈ B, U y * P j y = 0
  hUF : ∀ i ∈ range k, ∑ y ∈ B, U y * F i y = 0
  hVd : ∑ y ∈ B, V y * d y = 0
  hVT : ∑ y ∈ B, V y * T y = 0
  hVP : ∀ j ∈ Icc 1 (k - 1), ∑ y ∈ B, V y * P j y = 0
  hVF : ∀ i ∈ range k, ∑ y ∈ B, V y * F i y = 0
  hUU : ∑ y ∈ B, U y * U y = 8
  hUV : ∑ y ∈ B, U y * V y = -4
  hVV : ∑ y ∈ B, V y * V y = 2 * k + 2
  hUx₀ : U x₀ = 1
  hVx₀ : V x₀ = 0
  hcong : ∀ y ∈ B, U y + 2 * V y + T y + 2 * ∑ j ∈ Icc 1 (k - 1), P j y +
    2 * ∑ i ∈ range k, F i y ≡ 0 [ZMOD 2 * k]

variable {B : Finset ι} {k : ℕ} {d : ι → ℤ} {x₀ x₁ x₂ x₃ x₄ : ι} {a b : ℕ → ι}
  {δ₁ δ₂ δ₃ δ₄ ε : ℤ} {T : ι → ℤ} {P F : ℕ → ι → ℤ} {U V : ι → ℤ}

theorem Hyp.swap (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) :
    Hyp B k d x₀ x₁ x₃ x₂ a b δ₁ δ₃ δ₂ ε T P F U V :=
  { h with
    hx₂ := h.hx₃
    hx₃ := h.hx₂
    h02 := h.h03
    h03 := h.h02
    h12 := h.h13
    h13 := h.h12
    h23 := h.h23.symm
    ha_x := fun j hj => ⟨(h.ha_x j hj).1, (h.ha_x j hj).2.1, (h.ha_x j hj).2.2.2,
      (h.ha_x j hj).2.2.1⟩
    hδ₂ := h.hδ₃
    hδ₃ := h.hδ₂
    hT := by rw [h.hT, add_right_comm] }

theorem Hyp.T_apply (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) (y : ι) :
    T y = (if y = x₀ then 1 else 0) + δ₁ * (if y = x₁ then 1 else 0) +
      δ₂ * (if y = x₂ then 1 else 0) + δ₃ * (if y = x₃ then 1 else 0) := by
  rw [h.hT]
  simp [Pi.single_apply]

theorem Hyp.T_values (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) :
    T x₀ = 1 ∧ T x₁ = δ₁ ∧ T x₂ = δ₂ ∧ T x₃ = δ₃ ∧
      ∀ y, y ≠ x₀ → y ≠ x₁ → y ≠ x₂ → y ≠ x₃ → T y = 0 := by
  have h01 := h.h01
  have h02 := h.h02
  have h03 := h.h03
  have h12 := h.h12
  have h13 := h.h13
  have h23 := h.h23
  refine ⟨?_, ?_, ?_, ?_, fun y h0 h1 h2 h3 => ?_⟩ <;>
    simp [h.T_apply, h01.symm, h02.symm, h03.symm, h12.symm, h13.symm, h23.symm, *]

theorem Hyp.sum_mul_T (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) (f : ι → ℤ) :
    ∑ y ∈ B, f y * T y = f x₀ + δ₁ * f x₁ + δ₂ * f x₂ + δ₃ * f x₃ := by
  rw [h.hT, sum_mul_four f h.hx₀ h.hx₁ h.hx₂ h.hx₃]

theorem Hyp.sum_mul_P (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) (f : ι → ℤ) {j : ℕ}
    (hj : j ∈ Icc 1 (k - 1)) :
    ∑ y ∈ B, f y * P j y = f x₀ + δ₁ * f x₁ - δ₁ * f (a j) := by
  rw [h.hP j hj, sum_mul_three f h.hx₀ h.hx₁ (h.ha j hj)]

theorem Hyp.sum_mul_F (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) (f : ι → ℤ) {i : ℕ}
    (hi : i ∈ range k) : ∑ y ∈ B, f y * F i y = ε * (f (b i) - f (b 0)) := by
  rw [h.hF i hi, sum_mul_two f (h.hb i hi) (h.hb 0 (Finset.mem_range.mpr (by
    have := h.hk
    omega)))]

theorem Hyp.const_of_F (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) {f : ι → ℤ}
    (hf : ∀ i ∈ range k, ∑ y ∈ B, f y * F i y = 0) : ∀ i ∈ range k, f (b i) = f (b 0) := by
  intro i hi
  have e := hf i hi
  rw [h.sum_mul_F f hi] at e
  rcases mul_eq_zero.mp e with e | e
  · exact absurd e (sign_ne_zero h.hε)
  · linarith

theorem Hyp.even_U_add_T (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) {y : ι}
    (hy : y ∈ B) : Even (U y + T y) := by
  have h2 : (2 : ℤ) ∣ _ :=
    dvd_trans (dvd_mul_right 2 (k : ℤ)) (Int.modEq_zero_iff_dvd.mp (h.hcong y hy))
  rw [Int.even_iff]
  omega

theorem Hyp.U_shape (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) :
    ∃ x₄ ∈ B, x₀ ≠ x₄ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₄ ∧ x₃ ≠ x₄ ∧ ∃ δ₄ : ℤ, (δ₄ = 1 ∨ δ₄ = -1) ∧
      U x₄ = 2 * δ₄ ∧ (∀ y ∈ B, y ≠ x₀ → y ≠ x₁ → y ≠ x₂ → y ≠ x₃ → y ≠ x₄ → U y = 0) ∧
      U x₁ = -δ₁ ∧ ((U x₂ = δ₂ ∧ U x₃ = -δ₃) ∨ (U x₂ = -δ₂ ∧ U x₃ = δ₃)) ∧
      ∀ j ∈ Icc 1 (k - 1), a j ≠ x₄ := by
  obtain ⟨hTx₀, hTx₁, hTx₂, hTx₃, hT0⟩ := h.T_values
  have hodd : ∀ y ∈ B, ∀ δ : ℤ, (δ = 1 ∨ δ = -1) → T y = δ → Odd (U y) := by
    intro y hy δ hδ hTy
    have e := h.even_U_add_T hy
    rw [hTy, Int.even_iff] at e
    rw [Int.odd_iff]
    rcases hδ with rfl | rfl <;> omega
  obtain ⟨hv₁, hv₂, hv₃, x₄, hx₄, h40, h41, h42, h43, δ₄, hδ₄, hUx₄, hU0⟩ :=
    norm_eight_shape h.hx₀ h.hx₁ h.hx₂ h.hx₃ h.h01 h.h02 h.h03 h.h12 h.h13 h.h23 h.hUx₀
      (hodd _ h.hx₁ _ h.hδ₁ hTx₁) (hodd _ h.hx₂ _ h.hδ₂ hTx₂) (hodd _ h.hx₃ _ h.hδ₃ hTx₃)
      (fun y hy h0 h1 h2 h3 => by simpa [hT0 y h0 h1 h2 h3] using h.even_U_add_T hy) h.hUU
  have hUT := h.hUT
  rw [h.sum_mul_T U, h.hUx₀] at hUT
  have hUP : ∀ j ∈ Icc 1 (k - 1), 1 + δ₁ * U x₁ - δ₁ * U (a j) = 0 := fun j hj => by
    have e := h.hUP j hj
    rwa [h.sum_mul_P U hj, h.hUx₀] at e
  have hdT := h.hdT
  rw [h.sum_mul_T d, h.hdx₀] at hdT
  have hdP : ∀ j ∈ Icc 1 (k - 1), 1 + δ₁ * d x₁ - δ₁ * d (a j) = 0 := fun j hj => by
    have e := h.hdP j hj
    rwa [h.sum_mul_P d hj, h.hdx₀] at e
  have hUd : U x₀ * d x₀ + U x₁ * d x₁ + U x₂ * d x₂ + U x₃ * d x₃ + U x₄ * d x₄ = 0 := by
    rw [← h.hUd]
    exact (sum_eq_five (fun y => U y * d y) h.hx₀ h.hx₁ h.hx₂ h.hx₃ hx₄ h.h01 h.h02 h.h03
      h40.symm h.h12 h.h13 h41.symm h.h23 h42.symm h43.symm
      fun y hy h0 h1 h2 h3 h4 => by rw [hU0 y hy h0 h1 h2 h3 h4, zero_mul]).symm
  rw [h.hUx₀, h.hdx₀] at hUd
  have hδ₁sq := sign_mul_self h.hδ₁
  have hj1 : 1 ∈ Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by have := h.hk; omega⟩
  have hU₁ : U x₁ = -δ₁ := by
    by_contra hne
    have hU₁' : U x₁ = δ₁ := by
      rcases hv₁ with hu | hu <;> rcases h.hδ₁ with hδ | hδ <;> omega
    have e1 := hUP 1 hj1
    rw [hU₁', hδ₁sq] at e1
    have hUa : U (a 1) = 2 * δ₁ := by
      rcases h.hδ₁ with hδ | hδ <;> rw [hδ] at e1 ⊢ <;> linarith
    obtain ⟨ha0, ha1, ha2, ha3⟩ := h.ha_x 1 hj1
    have hax₄ : a 1 = x₄ := by
      by_contra hne'
      have e := hU0 (a 1) (h.ha 1 hj1) ha0 ha1 ha2 ha3 hne'
      rw [hUa] at e
      rcases h.hδ₁ with hδ | hδ <;> rw [hδ] at e <;> norm_num at e
    have hδ₄' : δ₄ = δ₁ := by
      rw [← hax₄, hUa] at hUx₄
      linarith
    rw [hU₁', hδ₁sq] at hUT
    have hU₂₃ : U x₂ = -δ₂ ∧ U x₃ = -δ₃ := by
      rcases hv₂ with h2 | h2 <;> rcases hv₃ with h3 | h3 <;> rcases h.hδ₂ with hd2 | hd2 <;>
        rcases h.hδ₃ with hd3 | hd3 <;> rw [h2, h3, hd2, hd3] at hUT ⊢ <;> omega
    rw [hU₁', hU₂₃.1, hU₂₃.2, hUx₄, hδ₄', ← hax₄] at hUd
    have hpos := h.hd (a 1) (h.ha 1 hj1)
    have e4 : 4 * δ₁ * d (a 1) = 0 := by linear_combination hUd + hdT - 2 * hdP 1 hj1
    rcases h.hδ₁ with hδ | hδ <;> rw [hδ] at e4 <;> linarith
  refine ⟨x₄, hx₄, h40.symm, h41.symm, h42.symm, h43.symm, δ₄, hδ₄, hUx₄, hU0, hU₁, ?_, ?_⟩
  · rw [hU₁, mul_neg, hδ₁sq] at hUT
    rcases hv₂ with h2 | h2 <;> rcases hv₃ with h3 | h3 <;> rcases h.hδ₂ with hd2 | hd2 <;>
      rcases h.hδ₃ with hd3 | hd3 <;> rw [h2, h3, hd2, hd3] at hUT ⊢ <;> omega
  · intro j hj hax
    have e := hUP j hj
    rw [hU₁, hax, hUx₄] at e
    rcases h.hδ₁ with hd1 | hd1 <;> rcases hδ₄ with hd4 | hd4 <;> rw [hd1, hd4] at e <;>
      norm_num at e

structure UShape (B : Finset ι) (k : ℕ) (x₀ x₁ x₂ x₃ x₄ : ι) (a : ℕ → ι) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (U : ι → ℤ) : Prop where
  hx₄ : x₄ ∈ B
  h04 : x₀ ≠ x₄
  h14 : x₁ ≠ x₄
  h24 : x₂ ≠ x₄
  h34 : x₃ ≠ x₄
  hδ₄ : δ₄ = 1 ∨ δ₄ = -1
  hUx₁ : U x₁ = -δ₁
  hUx₂ : U x₂ = δ₂
  hUx₃ : U x₃ = -δ₃
  hUx₄ : U x₄ = 2 * δ₄
  hU0 : ∀ y ∈ B, y ≠ x₀ → y ≠ x₁ → y ≠ x₂ → y ≠ x₃ → y ≠ x₄ → U y = 0
  ha₄ : ∀ j ∈ Icc 1 (k - 1), a j ≠ x₄

theorem Hyp.zero_one_mem (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V) :
    0 ∈ range k ∧ 1 ∈ range k ∧ b 1 ≠ b 0 := by
  have hk := h.hk
  have h0 : 0 ∈ range k := Finset.mem_range.mpr (by omega)
  have h1 : 1 ∈ range k := Finset.mem_range.mpr (by omega)
  exact ⟨h0, h1, fun e => absurd (h.hb_inj h1 h0 e) (by norm_num)⟩

theorem Hyp.b_avoid (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V)
    (hU : UShape B k x₀ x₁ x₂ x₃ x₄ a δ₁ δ₂ δ₃ δ₄ U) :
    ∀ i ∈ range k, b i ≠ x₂ ∧ b i ≠ x₃ ∧ b i ≠ x₄ := by
  obtain ⟨-, -, hTx₂, hTx₃, hT0⟩ := h.T_values
  have hTb := h.const_of_F h.hTF
  have hUb := h.const_of_F h.hUF
  obtain ⟨hb0, hb1, hne⟩ := h.zero_one_mem
  have hTb0 : T (b 0) = 0 := by
    by_contra hT
    have hs : ∀ i ∈ range k, b i = x₂ ∨ b i = x₃ := by
      intro i hi
      by_contra hc
      obtain ⟨hc2, hc3⟩ := not_or.mp hc
      exact hT (by rw [← hTb i hi]; exact hT0 _ (h.hb_x i hi).1 (h.hb_x i hi).2 hc2 hc3)
    have hT1 := hTb 1 hb1
    have hU1 := hUb 1 hb1
    rcases hs 0 hb0 with e0 | e0 <;> rcases hs 1 hb1 with e1 | e1
    · exact hne (e1.trans e0.symm)
    · rw [e0, e1, hTx₂, hTx₃] at hT1
      rw [e0, e1, hU.hUx₂, hU.hUx₃] at hU1
      rcases h.hδ₂ with hd | hd <;> omega
    · rw [e0, e1, hTx₂, hTx₃] at hT1
      rw [e0, e1, hU.hUx₂, hU.hUx₃] at hU1
      rcases h.hδ₂ with hd | hd <;> omega
    · exact hne (e1.trans e0.symm)
  have h23 : ∀ i ∈ range k, b i ≠ x₂ ∧ b i ≠ x₃ := by
    intro i hi
    have e := hTb i hi
    rw [hTb0] at e
    refine ⟨fun e' => ?_, fun e' => ?_⟩
    · rw [e', hTx₂] at e
      exact sign_ne_zero h.hδ₂ e
    · rw [e', hTx₃] at e
      exact sign_ne_zero h.hδ₃ e
  have hUb0 : U (b 0) = 0 := by
    by_contra hU'
    have hs : ∀ i ∈ range k, b i = x₄ := by
      intro i hi
      by_contra hc
      exact hU' (by
        rw [← hUb i hi]
        exact hU.hU0 _ (h.hb i hi) (h.hb_x i hi).1 (h.hb_x i hi).2 (h23 i hi).1 (h23 i hi).2 hc)
    exact hne ((hs 1 hb1).trans (hs 0 hb0).symm)
  intro i hi
  refine ⟨(h23 i hi).1, (h23 i hi).2, fun e' => ?_⟩
  have e := hUb i hi
  rw [hUb0, e', hU.hUx₄] at e
  rcases hU.hδ₄ with hd | hd <;> omega

theorem Hyp.cong_points (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V)
    (hU : UShape B k x₀ x₁ x₂ x₃ x₄ a δ₁ δ₂ δ₃ δ₄ U) :
    (2 * k : ℤ) ∣ 2 * V x₁ + 2 * ((k : ℤ) - 1) * δ₁ ∧ (2 * k : ℤ) ∣ 2 * V x₂ + 2 * δ₂ ∧
      (2 * k : ℤ) ∣ 2 * V x₄ + 2 * δ₄ ∧ (2 * k : ℤ) ∣ 2 * V (b 1) + 2 * ε := by
  obtain ⟨-, hTx₁, hTx₂, -, hT0⟩ := h.T_values
  have hbx := h.b_avoid hU
  obtain ⟨hb0, hb1, hne⟩ := h.zero_one_mem
  have hPsum0 : ∀ y, y ≠ x₀ → y ≠ x₁ → (∀ j ∈ Icc 1 (k - 1), y ≠ a j) →
      ∑ j ∈ Icc 1 (k - 1), P j y = 0 := by
    intro y h0 h1 ha'
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [h.hP j hj]
    simp [h0, h1, ha' j hj]
  have hPsum1 : ∑ j ∈ Icc 1 (k - 1), P j x₁ = ((k : ℤ) - 1) * δ₁ := by
    have e : ∀ j ∈ Icc 1 (k - 1), P j x₁ = δ₁ := fun j hj => by
      rw [h.hP j hj]
      simp [h.h01.symm, (h.ha_x j hj).2.1.symm]
    have hk := h.hk
    rw [Finset.sum_congr rfl e, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel,
      Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hFsum0 : ∀ y, (∀ i ∈ range k, y ≠ b i) → ∑ i ∈ range k, F i y = 0 := by
    intro y hb'
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [h.hF i hi]
    simp [hb' i hi, hb' 0 hb0]
  have hFsum1 : ∑ i ∈ range k, F i (b 1) = ε := by
    rw [Finset.sum_eq_single_of_mem 1 hb1]
    · rw [h.hF 1 hb1]
      simp [hne]
    · intro i hi hi1
      rw [h.hF i hi]
      have : b 1 ≠ b i := fun e => hi1 (h.hb_inj hi hb1 e.symm)
      simp [this, hne]
  have hc : ∀ y ∈ B, (2 * k : ℤ) ∣ U y + 2 * V y + T y + 2 * ∑ j ∈ Icc 1 (k - 1), P j y +
      2 * ∑ i ∈ range k, F i y := fun y hy => Int.modEq_zero_iff_dvd.mp (h.hcong y hy)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have c := hc x₁ h.hx₁
    rw [hU.hUx₁, hTx₁, hPsum1, hFsum0 x₁ fun i hi => (h.hb_x i hi).2.symm] at c
    convert c using 1
    ring
  · have c := hc x₂ h.hx₂
    rw [hU.hUx₂, hTx₂, hPsum0 x₂ h.h02.symm h.h12.symm fun j hj => (h.ha_x j hj).2.2.1.symm,
      hFsum0 x₂ fun i hi => (hbx i hi).1.symm] at c
    convert c using 1
    ring
  · have c := hc x₄ hU.hx₄
    rw [hU.hUx₄, hT0 x₄ hU.h04.symm hU.h14.symm hU.h24.symm hU.h34.symm,
      hPsum0 x₄ hU.h04.symm hU.h14.symm fun j hj => (hU.ha₄ j hj).symm,
      hFsum0 x₄ fun i hi => (hbx i hi).2.2.symm] at c
    convert c using 1
    ring
  · have c := hc (b 1) (h.hb 1 hb1)
    obtain ⟨hb10, hb11⟩ := h.hb_x 1 hb1
    obtain ⟨hb12, hb13, hb14⟩ := hbx 1 hb1
    rw [hU.hU0 _ (h.hb 1 hb1) hb10 hb11 hb12 hb13 hb14, hT0 _ hb10 hb11 hb12 hb13,
      hPsum0 _ hb10 hb11 fun j hj => h.hb_a 1 hb1 j hj, hFsum1] at c
    convert c using 1
    ring

theorem Hyp.V_values (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V)
    (hU : UShape B k x₀ x₁ x₂ x₃ x₄ a δ₁ δ₂ δ₃ δ₄ U) :
    V x₁ = δ₁ ∧ V x₂ = -δ₂ ∧ V x₄ = -δ₄ ∧ (∀ j ∈ Icc 1 (k - 1), V (a j) = δ₁) ∧
      (∀ i ∈ range k, V (b i) = V (b 0)) ∧ (V (b 0) = 1 ∨ V (b 0) = -1) ∧
      ∀ y ∈ B, y ≠ x₁ → y ≠ x₂ → y ≠ x₄ → (∀ j ∈ Icc 1 (k - 1), y ≠ a j) →
        (∀ i ∈ range k, y ≠ b i) → V y = 0 := by
  have hbx := h.b_avoid hU
  obtain ⟨hb0, hb1, -⟩ := h.zero_one_mem
  obtain ⟨c₁, c₂, c₄, cb⟩ := h.cong_points hU
  obtain ⟨m, hm⟩ := h.hk_even
  have h4 : (4 : ℤ) ∣ 2 * k := ⟨m, by rw [hm]; push_cast; ring⟩
  have hodd₁ : Odd (V x₁) := by
    have c := dvd_trans h4 c₁
    rw [hm] at c
    push_cast at c
    rw [Int.odd_iff]
    rcases h.hδ₁ with hd | hd <;> rw [hd] at c <;> omega
  have hodd₂ : Odd (V x₂) := by
    have c := dvd_trans h4 c₂
    rw [Int.odd_iff]
    rcases h.hδ₂ with hd | hd <;> rw [hd] at c <;> omega
  have hodd₄ : Odd (V x₄) := by
    have c := dvd_trans h4 c₄
    rw [Int.odd_iff]
    rcases hU.hδ₄ with hd | hd <;> rw [hd] at c <;> omega
  have hoddb : Odd (V (b 1)) := by
    have c := dvd_trans h4 cb
    rw [Int.odd_iff]
    rcases h.hε with hd | hd <;> rw [hd] at c <;> omega
  have hVa : ∀ j ∈ Icc 1 (k - 1), V (a j) = V x₁ := by
    intro j hj
    have e := h.hVP j hj
    rw [h.sum_mul_P V hj, h.hVx₀] at e
    rcases h.hδ₁ with hd | hd <;> rw [hd] at e <;> linarith
  have hVb := h.const_of_F h.hVF
  set D : Finset ι := insert x₁ (insert x₂ (insert x₄ ((Icc 1 (k - 1)).image a ∪
    (range k).image b))) with hD
  have hmemD : ∀ y, y ∈ D ↔ y = x₁ ∨ y = x₂ ∨ y = x₄ ∨ (∃ j ∈ Icc 1 (k - 1), a j = y) ∨
      ∃ i ∈ range k, b i = y := by
    intro y
    simp only [hD, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  have hDB : D ⊆ B := by
    intro y hy
    rcases (hmemD y).mp hy with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    exacts [h.hx₁, h.hx₂, hU.hx₄, h.ha j hj, h.hb i hi]
  have hDodd : ∀ y ∈ D, Odd (V y) := by
    intro y hy
    rcases (hmemD y).mp hy with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    · exact hodd₁
    · exact hodd₂
    · exact hodd₄
    · rw [hVa j hj]
      exact hodd₁
    · rw [hVb i hi, ← hVb 1 hb1]
      exact hoddb
  have hcard : #D = 2 * k + 2 := by
    have hA : #((Icc 1 (k - 1)).image a) = k - 1 := by
      rw [Finset.card_image_of_injOn h.ha_inj, Nat.card_Icc]
      omega
    have hB : #((range k).image b) = k := by
      rw [Finset.card_image_of_injOn h.hb_inj, Finset.card_range]
    have hdisj : Disjoint ((Icc 1 (k - 1)).image a) ((range k).image b) := by
      rw [Finset.disjoint_left]
      intro y hya hyb
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hya
      obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hyb
      exact h.hb_a i hi j hj e
    have hx₄n : x₄ ∉ (Icc 1 (k - 1)).image a ∪ (range k).image b := by
      simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
      exact ⟨fun j hj e => hU.ha₄ j hj e, fun i hi e => (hbx i hi).2.2 e⟩
    have hx₂n : x₂ ∉ insert x₄ ((Icc 1 (k - 1)).image a ∪ (range k).image b) := by
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or, not_exists,
        not_and]
      exact ⟨hU.h24, fun j hj e => (h.ha_x j hj).2.2.1 e, fun i hi e => (hbx i hi).1 e⟩
    have hx₁n : x₁ ∉ insert x₂ (insert x₄ ((Icc 1 (k - 1)).image a ∪ (range k).image b)) := by
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or, not_exists,
        not_and]
      exact ⟨h.h12, hU.h14, fun j hj e => (h.ha_x j hj).2.1 e, fun i hi e => (h.hb_x i hi).2 e⟩
    rw [hD, Finset.card_insert_of_notMem hx₁n, Finset.card_insert_of_notMem hx₂n,
      Finset.card_insert_of_notMem hx₄n, Finset.card_union_of_disjoint hdisj, hA, hB]
    have := h.hk
    omega
  obtain ⟨hpm, hzero⟩ := odd_support_of_norm_eq_card hDB hDodd (by
    rw [h.hVV, hcard]
    push_cast
    ring)
  have hV0 : ∀ y ∈ B, y ≠ x₁ → y ≠ x₂ → y ≠ x₄ → (∀ j ∈ Icc 1 (k - 1), y ≠ a j) →
      (∀ i ∈ range k, y ≠ b i) → V y = 0 := by
    intro y hy h1 h2 h4' ha' hb'
    refine hzero y hy fun hyD => ?_
    rcases (hmemD y).mp hyD with e | e | e | ⟨j, hj, e⟩ | ⟨i, hi, e⟩
    exacts [h1 e, h2 e, h4' e, ha' j hj e.symm, hb' i hi e.symm]
  have hVx₃ : V x₃ = 0 := hV0 x₃ h.hx₃ h.h13.symm h.h23.symm hU.h34
    (fun j hj e => (h.ha_x j hj).2.2.2 e.symm) fun i hi e => (hbx i hi).2.1 e.symm
  have hVT := h.hVT
  rw [h.sum_mul_T V, h.hVx₀, hVx₃] at hVT
  have hUV : U x₀ * V x₀ + U x₁ * V x₁ + U x₂ * V x₂ + U x₃ * V x₃ + U x₄ * V x₄ = -4 := by
    rw [← h.hUV]
    exact (sum_eq_five (fun y => U y * V y) h.hx₀ h.hx₁ h.hx₂ h.hx₃ hU.hx₄ h.h01 h.h02 h.h03
      hU.h04 h.h12 h.h13 hU.h14 h.h23 hU.h24 hU.h34
      fun y hy h0 h1 h2 h3 h4' => by rw [hU.hU0 y hy h0 h1 h2 h3 h4', zero_mul]).symm
  rw [h.hUx₀, hU.hUx₁, hU.hUx₂, hU.hUx₃, hU.hUx₄, h.hVx₀, hVx₃] at hUV
  have hv₁ := hpm x₁ ((hmemD x₁).mpr (Or.inl rfl))
  have hv₂ := hpm x₂ ((hmemD x₂).mpr (Or.inr (Or.inl rfl)))
  have hv₄ := hpm x₄ ((hmemD x₄).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hp : δ₁ * V x₁ = 1 ∨ δ₁ * V x₁ = -1 := by
    rcases hv₁ with e | e <;> rcases h.hδ₁ with hd | hd <;> rw [e, hd] <;> norm_num
  have hq : δ₂ * V x₂ = 1 ∨ δ₂ * V x₂ = -1 := by
    rcases hv₂ with e | e <;> rcases h.hδ₂ with hd | hd <;> rw [e, hd] <;> norm_num
  have hr : δ₄ * V x₄ = 1 ∨ δ₄ * V x₄ = -1 := by
    rcases hv₄ with e | e <;> rcases hU.hδ₄ with hd | hd <;> rw [e, hd] <;> norm_num
  have e₁ : δ₁ * V x₁ + δ₂ * V x₂ = 0 := by linear_combination hVT
  have e₂ : 2 * (δ₄ * V x₄) = 2 * (δ₁ * V x₁) - 4 := by linear_combination hUV - hVT
  have hp1 : δ₁ * V x₁ = 1 := by omega
  have hq1 : δ₂ * V x₂ = -1 := by omega
  have hr1 : δ₄ * V x₄ = -1 := by omega
  have hV₁ : V x₁ = δ₁ := by linear_combination δ₁ * hp1 - V x₁ * sign_mul_self h.hδ₁
  have hV₂ : V x₂ = -δ₂ := by linear_combination δ₂ * hq1 - V x₂ * sign_mul_self h.hδ₂
  have hV₄ : V x₄ = -δ₄ := by linear_combination δ₄ * hr1 - V x₄ * sign_mul_self hU.hδ₄
  refine ⟨hV₁, hV₂, hV₄, fun j hj => by rw [hVa j hj, hV₁], hVb,
    hpm _ ((hmemD (b 0)).mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨0, hb0, rfl⟩))))), hV0⟩

theorem Hyp.V_apply (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V)
    (hU : UShape B k x₀ x₁ x₂ x₃ x₄ a δ₁ δ₂ δ₃ δ₄ U) {σ : ℤ}
    (hσ : ∀ i ∈ range k, V (b i) = -σ) {y : ι} (hy : y ∈ B) :
    V y = (δ₁ • Pi.single x₁ 1 - δ₂ • Pi.single x₂ 1 - δ₄ • Pi.single x₄ 1 +
      δ₁ • ∑ j ∈ Icc 1 (k - 1), Pi.single (a j) 1 -
      σ • ∑ i ∈ range k, Pi.single (b i) 1 : ι → ℤ) y := by
  obtain ⟨hV₁, hV₂, hV₄, hVa, -, -, hV0⟩ := h.V_values hU
  have hbx := h.b_avoid hU
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases e1 : y = x₁
  · rw [e1, sum_single_apply_of_forall_ne fun j hj => (h.ha_x j hj).2.1.symm,
      sum_single_apply_of_forall_ne fun i hi => (h.hb_x i hi).2.symm]
    simp [h.h12, hU.h14, hV₁]
  by_cases e2 : y = x₂
  · rw [e2, sum_single_apply_of_forall_ne fun j hj => (h.ha_x j hj).2.2.1.symm,
      sum_single_apply_of_forall_ne fun i hi => (hbx i hi).1.symm]
    simp [h.h12.symm, hU.h24, hV₂]
  by_cases e4 : y = x₄
  · rw [e4, sum_single_apply_of_forall_ne fun j hj => (hU.ha₄ j hj).symm,
      sum_single_apply_of_forall_ne fun i hi => (hbx i hi).2.2.symm]
    simp [hU.h14.symm, hU.h24.symm, hV₄]
  by_cases ea : ∃ j ∈ Icc 1 (k - 1), y = a j
  · obtain ⟨j, hj, rfl⟩ := ea
    rw [sum_single_apply_of_injOn h.ha_inj hj,
      sum_single_apply_of_forall_ne fun i hi => (h.hb_a i hi j hj).symm]
    simp [(h.ha_x j hj).2.1, (h.ha_x j hj).2.2.1, hU.ha₄ j hj, hVa j hj]
  by_cases eb : ∃ i ∈ range k, y = b i
  · obtain ⟨i, hi, rfl⟩ := eb
    rw [sum_single_apply_of_forall_ne fun j hj => h.hb_a i hi j hj,
      sum_single_apply_of_injOn h.hb_inj hi]
    simp [(h.hb_x i hi).2, (hbx i hi).1, (hbx i hi).2.2, hσ i hi]
  have ea' : ∀ j ∈ Icc 1 (k - 1), y ≠ a j := fun j hj e => ea ⟨j, hj, e⟩
  have eb' : ∀ i ∈ range k, y ≠ b i := fun i hi e => eb ⟨i, hi, e⟩
  rw [sum_single_apply_of_forall_ne ea', sum_single_apply_of_forall_ne eb']
  simp [e1, e2, e4, hV0 y hy e1 e2 e4 ea' eb']

theorem Hyp.degrees (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V)
    (hU : UShape B k x₀ x₁ x₂ x₃ x₄ a δ₁ δ₂ δ₃ δ₄ U) :
    (∀ j ∈ Icc 1 (k - 1), d (a j) = d x₁ + δ₁) ∧ (∀ i ∈ range k, d (b i) = d x₁ + δ₁) ∧
      1 + δ₂ * d x₂ + δ₄ * d x₄ = 0 ∧ ∀ i ∈ range k, V (b i) = -δ₁ := by
  obtain ⟨-, -, -, -, hVb, hVb0, -⟩ := h.V_values hU
  obtain ⟨hb0, -, -⟩ := h.zero_one_mem
  have hk := h.hk
  have hj1 : 1 ∈ Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hda : ∀ j ∈ Icc 1 (k - 1), d (a j) = d x₁ + δ₁ := by
    intro j hj
    have e := h.hdP j hj
    rw [h.sum_mul_P d hj, h.hdx₀] at e
    rcases h.hδ₁ with hd | hd <;> rw [hd] at e ⊢ <;> linarith
  have hdb := h.const_of_F h.hdF
  have hdT := h.hdT
  rw [h.sum_mul_T d, h.hdx₀] at hdT
  have hUd : U x₀ * d x₀ + U x₁ * d x₁ + U x₂ * d x₂ + U x₃ * d x₃ + U x₄ * d x₄ = 0 := by
    rw [← h.hUd]
    exact (sum_eq_five (fun y => U y * d y) h.hx₀ h.hx₁ h.hx₂ h.hx₃ hU.hx₄ h.h01 h.h02 h.h03
      hU.h04 h.h12 h.h13 hU.h14 h.h23 hU.h24 hU.h34
      fun y hy h0 h1 h2 h3 h4 => by rw [hU.hU0 y hy h0 h1 h2 h3 h4, zero_mul]).symm
  rw [h.hUx₀, hU.hUx₁, hU.hUx₂, hU.hUx₃, hU.hUx₄, h.hdx₀] at hUd
  have hdeg : 1 + δ₂ * d x₂ + δ₄ * d x₄ = 0 := by
    have e : 2 * (1 + δ₂ * d x₂ + δ₄ * d x₄) = 0 := by linear_combination hdT + hUd
    linarith
  have hσ : ∀ i ∈ range k, V (b i) = -(-V (b 0)) := fun i hi => by rw [neg_neg, hVb i hi]
  have hdV : ∑ y ∈ B, (δ₁ • Pi.single x₁ 1 - δ₂ • Pi.single x₂ 1 - δ₄ • Pi.single x₄ 1 +
      δ₁ • ∑ j ∈ Icc 1 (k - 1), Pi.single (a j) 1 -
      (-V (b 0)) • ∑ i ∈ range k, Pi.single (b i) 1 : ι → ℤ) y * d y = 0 := by
    rw [← h.hVd]
    exact Finset.sum_congr rfl fun y hy => by rw [h.V_apply hU hσ hy]
  rw [sum_five_part_mul d h.hx₁ h.hx₂ hU.hx₄ h.ha h.hb, Finset.sum_congr rfl hda,
    Finset.sum_congr rfl hdb, Finset.sum_const, Finset.sum_const, Finset.card_range,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at hdV
  have key : (k : ℤ) * (δ₁ * (d x₁ + δ₁) + V (b 0) * d (b 0)) = 0 := by
    linear_combination hdV + hdeg + sign_mul_self h.hδ₁
  have hk0 : (k : ℤ) ≠ 0 := by
    have : (0 : ℤ) < k := by exact_mod_cast (by omega : 0 < k)
    exact this.ne'
  have key' : δ₁ * (d x₁ + δ₁) + V (b 0) * d (b 0) = 0 :=
    (mul_eq_zero.mp key).resolve_left hk0
  have hpa : 0 < d x₁ + δ₁ := by
    rw [← hda 1 hj1]
    exact h.hd _ (h.ha 1 hj1)
  have hpb : 0 < d (b 0) := h.hd _ (h.hb 0 hb0)
  have hfin : V (b 0) = -δ₁ ∧ d (b 0) = d x₁ + δ₁ := by
    rcases h.hδ₁ with hd | hd <;> rcases hVb0 with hv | hv <;> rw [hd, hv] at key' <;>
      rw [hd, hv] <;> constructor <;> linarith
  exact ⟨hda, fun i hi => by rw [hdb i hi, hfin.2], hdeg,
    fun i hi => by rw [hVb i hi, hfin.1]⟩

theorem Hyp.eps_eq (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V)
    (hU : UShape B k x₀ x₁ x₂ x₃ x₄ a δ₁ δ₂ δ₃ δ₄ U) (hk2 : k ≠ 2) : ε = δ₁ := by
  obtain ⟨-, -, -, cb⟩ := h.cong_points hU
  obtain ⟨-, hb1, -⟩ := h.zero_one_mem
  rw [(h.degrees hU).2.2.2 1 hb1] at cb
  have hdvd : (k : ℤ) ∣ ε - δ₁ := by
    have e : (2 * k : ℤ) ∣ 2 * (ε - δ₁) := by
      convert cb using 1
      ring
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp e
  have hk4 : (4 : ℤ) ≤ k := by
    obtain ⟨m, hm⟩ := h.hk_even
    have := h.hk
    omega
  have hlt : |ε - δ₁| < k := by
    rcases h.hε with e | e <;> rcases h.hδ₁ with hd | hd <;> rw [e, hd] <;> norm_num <;>
      linarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  linarith

theorem Hyp.body (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V)
    (hU : UShape B k x₀ x₁ x₂ x₃ x₄ a δ₁ δ₂ δ₃ δ₄ U) {b' : ℕ → ι} {ε' : ℤ}
    (hb'b : ∀ i ∈ range k, ∃ i' ∈ range k, b' i = b i')
    (hbb' : ∀ i ∈ range k, ∃ i' ∈ range k, b i = b' i')
    (hb'inj : Set.InjOn b' (range k))
    (hsum : ∑ i ∈ range k, (Pi.single (b' i) 1 : ι → ℤ) = ∑ i ∈ range k, Pi.single (b i) 1)
    (hF' : ∀ i ∈ range k, F i = ε' • (Pi.single (b' i) 1 - Pi.single (b' 0) 1))
    (hε' : ε' = δ₁) :
    ∃ x₄ ∈ B, ∃ δ₄ : ℤ, (δ₄ = 1 ∨ δ₄ = -1) ∧
      (x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₀ ≠ x₃ ∧ x₀ ≠ x₄ ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₃ ∧
        x₂ ≠ x₄ ∧ x₃ ≠ x₄) ∧
      Set.InjOn a (Icc 1 (k - 1)) ∧ Set.InjOn b' (range k) ∧
      (∀ j ∈ Icc 1 (k - 1), a j ≠ x₀ ∧ a j ≠ x₁ ∧ a j ≠ x₂ ∧ a j ≠ x₃ ∧ a j ≠ x₄) ∧
      (∀ i ∈ range k, b' i ≠ x₀ ∧ b' i ≠ x₁ ∧ b' i ≠ x₂ ∧ b' i ≠ x₃ ∧ b' i ≠ x₄) ∧
      (∀ i ∈ range k, ∀ j ∈ Icc 1 (k - 1), b' i ≠ a j) ∧
      ε' = δ₁ ∧
      (∀ y ∈ B, U y = (Pi.single x₀ 1 - δ₁ • Pi.single x₁ 1 + δ₂ • Pi.single x₂ 1 -
        δ₃ • Pi.single x₃ 1 + (2 * δ₄) • Pi.single x₄ 1 : ι → ℤ) y) ∧
      (∀ y ∈ B, V y = (δ₁ • Pi.single x₁ 1 - δ₂ • Pi.single x₂ 1 - δ₄ • Pi.single x₄ 1 +
        δ₁ • ∑ j ∈ Icc 1 (k - 1), Pi.single (a j) 1 -
        δ₁ • ∑ i ∈ range k, Pi.single (b' i) 1 : ι → ℤ) y) ∧
      (∀ j ∈ Icc 1 (k - 1), d (a j) = d x₁ + δ₁) ∧ (∀ i ∈ range k, d (b' i) = d x₁ + δ₁) ∧
      1 + δ₂ * d x₂ + δ₄ * d x₄ = 0 ∧
      (∀ y ∈ B, y ≠ x₀ → y ≠ x₁ → y ≠ x₂ → y ≠ x₃ → y ≠ x₄ →
        (∀ j ∈ Icc 1 (k - 1), y ≠ a j) → (∀ i ∈ range k, y ≠ b' i) → U y = 0 ∧ V y = 0) ∧
      T = Pi.single x₀ 1 + δ₁ • Pi.single x₁ 1 + δ₂ • Pi.single x₂ 1 + δ₃ • Pi.single x₃ 1 ∧
      ∀ i ∈ range k, F i = ε' • (Pi.single (b' i) 1 - Pi.single (b' 0) 1) := by
  obtain ⟨hda, hdb, hdeg, hVb⟩ := h.degrees hU
  obtain ⟨-, -, -, -, -, -, hV0⟩ := h.V_values hU
  have hbx := h.b_avoid hU
  refine ⟨x₄, hU.hx₄, δ₄, hU.hδ₄, ⟨h.h01, h.h02, h.h03, hU.h04, h.h12, h.h13, hU.h14, h.h23,
    hU.h24, hU.h34⟩, h.ha_inj, hb'inj, fun j hj => ⟨(h.ha_x j hj).1, (h.ha_x j hj).2.1,
    (h.ha_x j hj).2.2.1, (h.ha_x j hj).2.2.2, hU.ha₄ j hj⟩, ?_, ?_, hε', ?_, ?_, hda, ?_, hdeg,
    ?_, h.hT, hF'⟩
  · intro i hi
    obtain ⟨i', hi', e⟩ := hb'b i hi
    rw [e]
    exact ⟨(h.hb_x i' hi').1, (h.hb_x i' hi').2, (hbx i' hi').1, (hbx i' hi').2.1,
      (hbx i' hi').2.2⟩
  · intro i hi j hj
    obtain ⟨i', hi', e⟩ := hb'b i hi
    rw [e]
    exact h.hb_a i' hi' j hj
  · intro y hy
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases e0 : y = x₀
    · rw [e0]
      simp [h.h01, h.h02, h.h03, hU.h04, h.hUx₀]
    by_cases e1 : y = x₁
    · rw [e1]
      simp [h.h01.symm, h.h12, h.h13, hU.h14, hU.hUx₁]
    by_cases e2 : y = x₂
    · rw [e2]
      simp [h.h02.symm, h.h12.symm, h.h23, hU.h24, hU.hUx₂]
    by_cases e3 : y = x₃
    · rw [e3]
      simp [h.h03.symm, h.h13.symm, h.h23.symm, hU.h34, hU.hUx₃]
    by_cases e4 : y = x₄
    · rw [e4]
      simp [hU.h04.symm, hU.h14.symm, hU.h24.symm, hU.h34.symm, hU.hUx₄]
    simp [e0, e1, e2, e3, e4, hU.hU0 y hy e0 e1 e2 e3 e4]
  · intro y hy
    rw [hsum]
    exact h.V_apply hU hVb hy
  · intro i hi
    obtain ⟨i', hi', e⟩ := hb'b i hi
    rw [e]
    exact hdb i' hi'
  · intro y hy h0 h1 h2 h3 h4 ha' hb''
    have hb2 : ∀ i ∈ range k, y ≠ b i := by
      intro i hi
      obtain ⟨i', hi', e⟩ := hbb' i hi
      rw [e]
      exact hb'' i' hi'
    exact ⟨hU.hU0 y hy h0 h1 h2 h3 h4, hV0 y hy h1 h2 h4 ha' hb2⟩

theorem swap_mem_range_two {i : ℕ} (hi : i ∈ range 2) : Equiv.swap 0 1 i ∈ range 2 := by
  have : i = 0 ∨ i = 1 := by
    rw [Finset.mem_range] at hi
    omega
  rcases this with rfl | rfl <;> simp

theorem Hyp.core (h : Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V)
    (hU : UShape B k x₀ x₁ x₂ x₃ x₄ a δ₁ δ₂ δ₃ δ₄ U) :
    ∃ (b' : ℕ → ι) (ε' : ℤ), ((b' = b ∧ ε' = ε) ∨ (k = 2 ∧ b' = b ∘ Equiv.swap 0 1 ∧ ε' = -ε)) ∧
    ∃ x₄ ∈ B, ∃ δ₄ : ℤ, (δ₄ = 1 ∨ δ₄ = -1) ∧
      (x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₀ ≠ x₃ ∧ x₀ ≠ x₄ ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₃ ∧
        x₂ ≠ x₄ ∧ x₃ ≠ x₄) ∧
      Set.InjOn a (Icc 1 (k - 1)) ∧ Set.InjOn b' (range k) ∧
      (∀ j ∈ Icc 1 (k - 1), a j ≠ x₀ ∧ a j ≠ x₁ ∧ a j ≠ x₂ ∧ a j ≠ x₃ ∧ a j ≠ x₄) ∧
      (∀ i ∈ range k, b' i ≠ x₀ ∧ b' i ≠ x₁ ∧ b' i ≠ x₂ ∧ b' i ≠ x₃ ∧ b' i ≠ x₄) ∧
      (∀ i ∈ range k, ∀ j ∈ Icc 1 (k - 1), b' i ≠ a j) ∧
      ε' = δ₁ ∧
      (∀ y ∈ B, U y = (Pi.single x₀ 1 - δ₁ • Pi.single x₁ 1 + δ₂ • Pi.single x₂ 1 -
        δ₃ • Pi.single x₃ 1 + (2 * δ₄) • Pi.single x₄ 1 : ι → ℤ) y) ∧
      (∀ y ∈ B, V y = (δ₁ • Pi.single x₁ 1 - δ₂ • Pi.single x₂ 1 - δ₄ • Pi.single x₄ 1 +
        δ₁ • ∑ j ∈ Icc 1 (k - 1), Pi.single (a j) 1 -
        δ₁ • ∑ i ∈ range k, Pi.single (b' i) 1 : ι → ℤ) y) ∧
      (∀ j ∈ Icc 1 (k - 1), d (a j) = d x₁ + δ₁) ∧ (∀ i ∈ range k, d (b' i) = d x₁ + δ₁) ∧
      1 + δ₂ * d x₂ + δ₄ * d x₄ = 0 ∧
      (∀ y ∈ B, y ≠ x₀ → y ≠ x₁ → y ≠ x₂ → y ≠ x₃ → y ≠ x₄ →
        (∀ j ∈ Icc 1 (k - 1), y ≠ a j) → (∀ i ∈ range k, y ≠ b' i) → U y = 0 ∧ V y = 0) ∧
      T = Pi.single x₀ 1 + δ₁ • Pi.single x₁ 1 + δ₂ • Pi.single x₂ 1 + δ₃ • Pi.single x₃ 1 ∧
      ∀ i ∈ range k, F i = ε' • (Pi.single (b' i) 1 - Pi.single (b' 0) 1) := by
  by_cases hεδ : ε = δ₁
  · exact ⟨b, ε, Or.inl ⟨rfl, rfl⟩, h.body hU (fun i hi => ⟨i, hi, rfl⟩)
      (fun i hi => ⟨i, hi, rfl⟩) h.hb_inj rfl h.hF hεδ⟩
  have hk2 : k = 2 := by
    by_contra hk2
    exact hεδ (h.eps_eq hU hk2)
  have hεn : -ε = δ₁ := by
    rcases h.hε with e | e <;> rcases h.hδ₁ with hd | hd <;> omega
  have hmem : ∀ i ∈ range k, Equiv.swap 0 1 i ∈ range k := fun i hi => by
    rw [hk2] at hi ⊢
    exact swap_mem_range_two hi
  refine ⟨b ∘ Equiv.swap 0 1, -ε, Or.inr ⟨hk2, rfl, rfl⟩, h.body hU ?_ ?_ ?_ ?_ ?_ hεn⟩
  · exact fun i hi => ⟨Equiv.swap 0 1 i, hmem i hi, rfl⟩
  · exact fun i hi => ⟨Equiv.swap 0 1 i, hmem i hi, by simp⟩
  · intro i hi i' hi' e
    exact (Equiv.swap 0 1).injective (h.hb_inj (hmem i hi) (hmem i' hi') e)
  · rw [hk2]
    simp [Finset.sum_range_succ, add_comm]
  · intro i hi
    have hF := h.hF
    rw [hk2] at hi hF
    have : i = 0 ∨ i = 1 := by
      rw [Finset.mem_range] at hi
      omega
    rcases this with rfl | rfl
    · rw [hF 0 hi]
      simp
    · rw [hF 1 hi]
      simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [neg_smul, ← smul_neg, neg_sub]

end ColumnRigidity

theorem integral_principal_column_rigidity (B : Finset ι) (k : ℕ) (hk : 2 ≤ k)
    (hk_even : Even k) (d : ι → ℤ) (hd : ∀ y ∈ B, 0 < d y) (x₀ x₁ x₂ x₃ : ι) (hx₀ : x₀ ∈ B)
    (hx₁ : x₁ ∈ B) (hx₂ : x₂ ∈ B) (hx₃ : x₃ ∈ B) (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂)
    (h03 : x₀ ≠ x₃) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) (hdx₀ : d x₀ = 1)
    (a : ℕ → ι) (ha : ∀ j ∈ Icc 1 (k - 1), a j ∈ B) (ha_inj : Set.InjOn a (Icc 1 (k - 1)))
    (ha_x : ∀ j ∈ Icc 1 (k - 1), a j ≠ x₀ ∧ a j ≠ x₁ ∧ a j ≠ x₂ ∧ a j ≠ x₃) (b : ℕ → ι)
    (hb : ∀ i ∈ range k, b i ∈ B) (hb_inj : Set.InjOn b (range k))
    (hb_x : ∀ i ∈ range k, b i ≠ x₀ ∧ b i ≠ x₁)
    (hb_a : ∀ i ∈ range k, ∀ j ∈ Icc 1 (k - 1), b i ≠ a j) (δ₁ δ₂ δ₃ ε : ℤ)
    (hδ₁ : δ₁ = 1 ∨ δ₁ = -1) (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hδ₃ : δ₃ = 1 ∨ δ₃ = -1)
    (hε : ε = 1 ∨ ε = -1) (T : ι → ℤ)
    (hT : T = Pi.single x₀ 1 + δ₁ • Pi.single x₁ 1 + δ₂ • Pi.single x₂ 1 +
      δ₃ • Pi.single x₃ 1)
    (P : ℕ → ι → ℤ)
    (hP : ∀ j ∈ Icc 1 (k - 1),
      P j = Pi.single x₀ 1 + δ₁ • Pi.single x₁ 1 - δ₁ • Pi.single (a j) 1)
    (F : ℕ → ι → ℤ) (hF : ∀ i ∈ range k, F i = ε • (Pi.single (b i) 1 - Pi.single (b 0) 1))
    (hdT : ∑ y ∈ B, d y * T y = 0) (hdP : ∀ j ∈ Icc 1 (k - 1), ∑ y ∈ B, d y * P j y = 0)
    (hdF : ∀ i ∈ range k, ∑ y ∈ B, d y * F i y = 0)
    (hTF : ∀ i ∈ range k, ∑ y ∈ B, T y * F i y = 0)
    (hPF : ∀ j ∈ Icc 1 (k - 1), ∀ i ∈ range k, ∑ y ∈ B, P j y * F i y = 0) (U V : ι → ℤ)
    (hUd : ∑ y ∈ B, U y * d y = 0) (hUT : ∑ y ∈ B, U y * T y = 0)
    (hUP : ∀ j ∈ Icc 1 (k - 1), ∑ y ∈ B, U y * P j y = 0)
    (hUF : ∀ i ∈ range k, ∑ y ∈ B, U y * F i y = 0) (hVd : ∑ y ∈ B, V y * d y = 0)
    (hVT : ∑ y ∈ B, V y * T y = 0) (hVP : ∀ j ∈ Icc 1 (k - 1), ∑ y ∈ B, V y * P j y = 0)
    (hVF : ∀ i ∈ range k, ∑ y ∈ B, V y * F i y = 0) (hUU : ∑ y ∈ B, U y * U y = 8)
    (hUV : ∑ y ∈ B, U y * V y = -4) (hVV : ∑ y ∈ B, V y * V y = 2 * k + 2) (hUx₀ : U x₀ = 1)
    (hVx₀ : V x₀ = 0)
    (hcong : ∀ y ∈ B, U y + 2 * V y + T y + 2 * ∑ j ∈ Icc 1 (k - 1), P j y +
      2 * ∑ i ∈ range k, F i y ≡ 0 [ZMOD 2 * k]) :
    ∃ (y₂ y₃ : ι) (η₂ η₃ : ℤ),
      ((y₂ = x₂ ∧ η₂ = δ₂ ∧ y₃ = x₃ ∧ η₃ = δ₃) ∨ (y₂ = x₃ ∧ η₂ = δ₃ ∧ y₃ = x₂ ∧ η₃ = δ₂)) ∧
    ∃ (b' : ℕ → ι) (ε' : ℤ), ((b' = b ∧ ε' = ε) ∨ (k = 2 ∧ b' = b ∘ Equiv.swap 0 1 ∧ ε' = -ε)) ∧
    ∃ x₄ ∈ B, ∃ δ₄ : ℤ, (δ₄ = 1 ∨ δ₄ = -1) ∧
      (x₀ ≠ x₁ ∧ x₀ ≠ y₂ ∧ x₀ ≠ y₃ ∧ x₀ ≠ x₄ ∧ x₁ ≠ y₂ ∧ x₁ ≠ y₃ ∧ x₁ ≠ x₄ ∧ y₂ ≠ y₃ ∧
        y₂ ≠ x₄ ∧ y₃ ≠ x₄) ∧
      Set.InjOn a (Icc 1 (k - 1)) ∧ Set.InjOn b' (range k) ∧
      (∀ j ∈ Icc 1 (k - 1), a j ≠ x₀ ∧ a j ≠ x₁ ∧ a j ≠ y₂ ∧ a j ≠ y₃ ∧ a j ≠ x₄) ∧
      (∀ i ∈ range k, b' i ≠ x₀ ∧ b' i ≠ x₁ ∧ b' i ≠ y₂ ∧ b' i ≠ y₃ ∧ b' i ≠ x₄) ∧
      (∀ i ∈ range k, ∀ j ∈ Icc 1 (k - 1), b' i ≠ a j) ∧
      ε' = δ₁ ∧
      (∀ y ∈ B, U y = (Pi.single x₀ 1 - δ₁ • Pi.single x₁ 1 + η₂ • Pi.single y₂ 1 -
        η₃ • Pi.single y₃ 1 + (2 * δ₄) • Pi.single x₄ 1 : ι → ℤ) y) ∧
      (∀ y ∈ B, V y = (δ₁ • Pi.single x₁ 1 - η₂ • Pi.single y₂ 1 - δ₄ • Pi.single x₄ 1 +
        δ₁ • ∑ j ∈ Icc 1 (k - 1), Pi.single (a j) 1 -
        δ₁ • ∑ i ∈ range k, Pi.single (b' i) 1 : ι → ℤ) y) ∧
      (∀ j ∈ Icc 1 (k - 1), d (a j) = d x₁ + δ₁) ∧ (∀ i ∈ range k, d (b' i) = d x₁ + δ₁) ∧
      1 + η₂ * d y₂ + δ₄ * d x₄ = 0 ∧
      (∀ y ∈ B, y ≠ x₀ → y ≠ x₁ → y ≠ y₂ → y ≠ y₃ → y ≠ x₄ →
        (∀ j ∈ Icc 1 (k - 1), y ≠ a j) → (∀ i ∈ range k, y ≠ b' i) → U y = 0 ∧ V y = 0) ∧
      T = Pi.single x₀ 1 + δ₁ • Pi.single x₁ 1 + η₂ • Pi.single y₂ 1 + η₃ • Pi.single y₃ 1 ∧
      ∀ i ∈ range k, F i = ε' • (Pi.single (b' i) 1 - Pi.single (b' 0) 1) := by
  have h : ColumnRigidity.Hyp B k d x₀ x₁ x₂ x₃ a b δ₁ δ₂ δ₃ ε T P F U V :=
    ⟨hk, hk_even, hd, hx₀, hx₁, hx₂, hx₃, h01, h02, h03, h12, h13, h23, hdx₀, ha, ha_inj, ha_x,
      hb, hb_inj, hb_x, hb_a, hδ₁, hδ₂, hδ₃, hε, hT, hP, hF, hdT, hdP, hdF, hTF, hPF, hUd, hUT,
      hUP, hUF, hVd, hVT, hVP, hVF, hUU, hUV, hVV, hUx₀, hVx₀, hcong⟩
  obtain ⟨x₄, hx₄, h04, h14, h24, h34, δ₄, hδ₄, hUx₄, hU0, hUx₁, hU23, ha₄⟩ := h.U_shape
  rcases hU23 with ⟨hUx₂, hUx₃⟩ | ⟨hUx₂, hUx₃⟩
  · exact ⟨x₂, x₃, δ₂, δ₃, Or.inl ⟨rfl, rfl, rfl, rfl⟩,
      h.core ⟨hx₄, h04, h14, h24, h34, hδ₄, hUx₁, hUx₂, hUx₃, hUx₄, hU0, ha₄⟩⟩
  · exact ⟨x₃, x₂, δ₃, δ₂, Or.inr ⟨rfl, rfl, rfl, rfl⟩,
      h.swap.core ⟨hx₄, h04, h14, h34, h24, hδ₄, hUx₁, hUx₃, hUx₂, hUx₄,
        fun y hy h0 h1 h3 h2 h4 => hU0 y hy h0 h1 h2 h3 h4, ha₄⟩⟩

end CFSG.Semidihedral.Principal
