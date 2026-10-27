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

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.PZ

open Subgroup

section Cycle

variable {G : Type*} [Group G]

@[expose] def cj (x ℓ : G) (i : ℕ) : G := x ^ i * ℓ * (x ^ i)⁻¹

theorem cj_zero (x ℓ : G) : cj x ℓ 0 = ℓ := by simp [cj]

theorem cj_add (x ℓ : G) (i j : ℕ) : cj x ℓ (i + j) = x ^ i * cj x ℓ j * (x ^ i)⁻¹ := by
  simp only [cj, pow_add]
  group

theorem cj_succ (x ℓ : G) (i : ℕ) : cj x ℓ (i + 1) = x * cj x ℓ i * x⁻¹ := by
  have h := cj_add x ℓ 1 i
  rw [add_comm] at h
  simpa using h

theorem cj_add_five {x : G} (hx5 : x ^ 5 = 1) (ℓ : G) (j : ℕ) :
    cj x ℓ (j + 5) = cj x ℓ j := by
  have h := cj_add x ℓ 5 j
  rw [add_comm] at h
  rw [h, hx5]
  simp

theorem cj_mem {E : Subgroup G} {x ℓ : G} (hx : ∀ e ∈ E, x * e * x⁻¹ ∈ E) (hℓ : ℓ ∈ E) :
    ∀ i : ℕ, cj x ℓ i ∈ E := by
  intro i
  induction i with
  | zero => rw [cj_zero]; exact hℓ
  | succ n ih => rw [cj_succ]; exact hx _ ih

end Cycle

section Five

variable {G : Type*} [Group G]

structure FiveData (E : Subgroup G) (x z ℓ₀ : G) : Prop where
  comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  sq : ∀ e ∈ E, e * e = 1
  norm : ∀ e ∈ E, x * e * x⁻¹ ∈ E
  x5 : x ^ 5 = 1
  z_mem : z ∈ E
  z_ne : z ≠ 1
  xz : x * z = z * x
  cent : ∀ e ∈ E, x * e = e * x → e = 1 ∨ e = z
  ℓ_mem : ℓ₀ ∈ E
  ℓ_ne_one : ℓ₀ ≠ 1
  ℓ_ne_z : ℓ₀ ≠ z

variable {E : Subgroup G} {x z ℓ₀ : G}

theorem FiveData.mem (h : FiveData E x z ℓ₀) (i : ℕ) : cj x ℓ₀ i ∈ E :=
  cj_mem h.norm h.ℓ_mem i

theorem FiveData.sq_cj (h : FiveData E x z ℓ₀) (i : ℕ) : cj x ℓ₀ i * cj x ℓ₀ i = 1 :=
  h.sq _ (h.mem i)

theorem FiveData.z_sq (h : FiveData E x z ℓ₀) : z * z = 1 := h.sq _ h.z_mem

theorem FiveData.x_comm_w (h : FiveData E x z ℓ₀) {w : G} (hw : w = 1 ∨ w = z) : x * w = w * x := by
  rcases hw with rfl | rfl
  · simp
  · exact h.xz

theorem FiveData.w_sq (h : FiveData E x z ℓ₀) {w : G} (hw : w = 1 ∨ w = z) : w * w = 1 := by
  rcases hw with rfl | rfl
  · simp
  · exact h.z_sq

theorem FiveData.mul_ne (h : FiveData E x z ℓ₀) {i j : ℕ} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) :
    cj x ℓ₀ i * cj x ℓ₀ j ≠ 1 ∧ cj x ℓ₀ i * cj x ℓ₀ j ≠ z := by
  have key : ∀ w : G, (w = 1 ∨ w = z) → cj x ℓ₀ i * cj x ℓ₀ j = w → False := by
    intro w hw hprod
    have hww := h.w_sq hw
    have hxw := h.x_comm_w hw
    have hxk : ∀ k : ℕ, x ^ k * w = w * x ^ k := fun k => ((Commute.pow_left (show Commute x w from hxw) k)).eq
    obtain ⟨m, hm1, hm4, hmij⟩ : ∃ m : ℕ, 1 ≤ m ∧ m ≤ 4 ∧ (i + m = j ∨ i + m = j + 5) := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact ⟨j - i, by omega, by omega, Or.inl (by omega)⟩
      · exact ⟨j + 5 - i, by omega, by omega, Or.inr (by omega)⟩
    have hcj : cj x ℓ₀ (i + m) = cj x ℓ₀ j := by
      rcases hmij with h1 | h1
      · rw [h1]
      · rw [h1]
        exact cj_add_five h.x5 ℓ₀ j
    have hcjj : cj x ℓ₀ j = cj x ℓ₀ i * w := by
      have h2 := h.sq_cj i
      calc cj x ℓ₀ j = cj x ℓ₀ i * (cj x ℓ₀ i * cj x ℓ₀ j) := by rw [← mul_assoc, h2, one_mul]
        _ = cj x ℓ₀ i * w := by rw [hprod]
    have hcm : cj x ℓ₀ m = ℓ₀ * w := by
      have h1 := cj_add x ℓ₀ i m
      rw [hcj, hcjj] at h1
      have h3 : cj x ℓ₀ m = (x ^ i)⁻¹ * (cj x ℓ₀ i * w) * x ^ i := by
        rw [h1]
        group
      rw [h3]
      have h4 : cj x ℓ₀ i = x ^ i * ℓ₀ * (x ^ i)⁻¹ := rfl
      rw [h4]
      calc (x ^ i)⁻¹ * (x ^ i * ℓ₀ * (x ^ i)⁻¹ * w) * x ^ i
          = ℓ₀ * ((x ^ i)⁻¹ * w * x ^ i) := by group
        _ = ℓ₀ * w := by
          congr 1
          rw [mul_assoc, ← hxk i, inv_mul_cancel_left]
    have hiter : ∀ k : ℕ, cj x ℓ₀ (m * k) = ℓ₀ * w ^ k := by
      intro k
      induction k with
      | zero => simp [cj_zero]
      | succ n ih =>
        have e1 : m * (n + 1) = m * n + m := by ring
        rw [e1, cj_add, hcm]
        have hc : cj x ℓ₀ (m * n) = x ^ (m * n) * ℓ₀ * (x ^ (m * n))⁻¹ := rfl
        calc x ^ (m * n) * (ℓ₀ * w) * (x ^ (m * n))⁻¹
            = (x ^ (m * n) * ℓ₀ * (x ^ (m * n))⁻¹) * (x ^ (m * n) * w * (x ^ (m * n))⁻¹) := by
              group
          _ = ℓ₀ * w ^ n * w := by
            rw [← hc, ih, hxk (m * n)]
            group
          _ = ℓ₀ * w ^ (n + 1) := by rw [pow_succ, mul_assoc]
    have h5 : cj x ℓ₀ (m * 5) = ℓ₀ := by
      have : x ^ (m * 5) = 1 := by rw [mul_comm, pow_mul, h.x5, one_pow]
      simp [cj, this]
    have hw1 : w = 1 := by
      have h6 := hiter 5
      rw [h5] at h6
      have hw2 : w ^ 2 = 1 := by rw [pow_two]; exact hww
      have h7 : w ^ 5 = w := by
        calc w ^ 5 = (w ^ 2) ^ 2 * w := by rw [← pow_mul, ← pow_succ]
          _ = w := by rw [hw2]; simp
      rw [h7] at h6
      have : ℓ₀ * w = ℓ₀ * 1 := by rw [← h6, mul_one]
      exact mul_left_cancel this
    rw [hw1, mul_one] at hcm
    have hcomm : Commute (x ^ m) ℓ₀ := by
      have h8 : x ^ m * ℓ₀ * (x ^ m)⁻¹ = ℓ₀ := hcm
      exact mul_inv_eq_iff_eq_mul.1 h8
    have hx : Commute x ℓ₀ := by
      have hpow : ∀ q : ℕ, x ^ (5 * q + 1) = x := fun q => by
        rw [pow_succ, pow_mul, h.x5, one_pow, one_mul]
      obtain ⟨m', hm'⟩ : ∃ m' : ℕ, x = (x ^ m) ^ m' := by
        interval_cases m
        · exact ⟨1, by simp⟩
        · exact ⟨3, by rw [← pow_mul]; exact (hpow 1).symm⟩
        · exact ⟨2, by rw [← pow_mul]; exact (hpow 1).symm⟩
        · exact ⟨4, by rw [← pow_mul]; exact (hpow 3).symm⟩
      rw [hm']
      exact hcomm.pow_left m'
    rcases h.cent ℓ₀ h.ℓ_mem hx.eq with h9 | h9
    · exact h.ℓ_ne_one h9
    · exact h.ℓ_ne_z h9
  exact ⟨fun h1 => key 1 (Or.inl rfl) h1, fun h1 => key z (Or.inr rfl) h1⟩

theorem FiveData.prod_mem (h : FiveData E x z ℓ₀) :
    cj x ℓ₀ 0 * cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4 = 1 ∨
      cj x ℓ₀ 0 * cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4 = z := by
  have hP : cj x ℓ₀ 0 * cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4 ∈ E :=
    mul_mem (mul_mem (mul_mem (mul_mem (h.mem 0) (h.mem 1)) (h.mem 2)) (h.mem 3)) (h.mem 4)
  have hshift : x * (cj x ℓ₀ 0 * cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4) * x⁻¹ =
      cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4 * cj x ℓ₀ 0 := by
    have e5 : cj x ℓ₀ 5 = cj x ℓ₀ 0 := cj_add_five h.x5 ℓ₀ 0
    have e1 := cj_succ x ℓ₀ 0
    have e2 := cj_succ x ℓ₀ 1
    have e3 := cj_succ x ℓ₀ 2
    have e4 := cj_succ x ℓ₀ 3
    have e6 := cj_succ x ℓ₀ 4
    rw [e5] at e6
    calc x * (cj x ℓ₀ 0 * cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4) * x⁻¹
        = (x * cj x ℓ₀ 0 * x⁻¹) * (x * cj x ℓ₀ 1 * x⁻¹) * (x * cj x ℓ₀ 2 * x⁻¹) *
          (x * cj x ℓ₀ 3 * x⁻¹) * (x * cj x ℓ₀ 4 * x⁻¹) := by group
      _ = _ := by rw [← e1, ← e2, ← e3, ← e4, ← e6]
  have hcomm : x * (cj x ℓ₀ 0 * cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4) =
      (cj x ℓ₀ 0 * cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4) * x := by
    have h1 : cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4 * cj x ℓ₀ 0 =
        cj x ℓ₀ 0 * cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4 := by
      have hc : cj x ℓ₀ 0 * (cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4) =
          (cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4) * cj x ℓ₀ 0 :=
        h.comm _ (h.mem 0) _ (mul_mem (mul_mem (mul_mem (h.mem 1) (h.mem 2)) (h.mem 3)) (h.mem 4))
      calc cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4 * cj x ℓ₀ 0
          = cj x ℓ₀ 0 * (cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4) := hc.symm
        _ = _ := by group
    exact mul_inv_eq_iff_eq_mul.1 (hshift.trans h1)
  rcases h.cent _ hP hcomm with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

theorem prod_complement {C : Type*} [CommGroup C] (c : ℕ → C) {i j k : ℕ} (hi : i < 5) (hj : j < 5)
    (hk : k < 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ p q : ℕ, p < 5 ∧ q < 5 ∧ p ≠ q ∧ c i * c j * c k * (c p * c q) =
      c 0 * c 1 * c 2 * c 3 * c 4 := by
  classical
  have hS : ({i, j, k} : Finset ℕ) ⊆ Finset.range 5 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_range]
    rcases ha with rfl | rfl | rfl <;> assumption
  have hnij : i ∉ ({j, k} : Finset ℕ) := by simp [hij, hik]
  have hnjk : j ∉ ({k} : Finset ℕ) := by simp [hjk]
  have hcardS : ({i, j, k} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem hnij, Finset.card_insert_of_notMem hnjk, Finset.card_singleton]
  have hT : (Finset.range 5 \ {i, j, k}).card = 2 := by
    rw [Finset.card_sdiff_of_subset hS, hcardS]
    simp
  obtain ⟨p, q, hpq, hTpq⟩ := Finset.card_eq_two.1 hT
  have hp : p ∈ Finset.range 5 := by
    have : p ∈ Finset.range 5 \ {i, j, k} := by rw [hTpq]; simp
    exact (Finset.mem_sdiff.1 this).1
  have hq : q ∈ Finset.range 5 := by
    have : q ∈ Finset.range 5 \ {i, j, k} := by rw [hTpq]; simp
    exact (Finset.mem_sdiff.1 this).1
  refine ⟨p, q, Finset.mem_range.1 hp, Finset.mem_range.1 hq, hpq, ?_⟩
  have hprod := Finset.prod_sdiff (f := c) hS
  rw [hTpq, Finset.prod_pair hpq, Finset.prod_insert hnij, Finset.prod_insert hnjk,
    Finset.prod_singleton] at hprod
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at hprod
  calc c i * c j * c k * (c p * c q) = c p * c q * (c i * (c j * c k)) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = _ := hprod

theorem FiveData.no_triple (h : FiveData E x z ℓ₀) {i j k : ℕ} (hi : i < 5) (hj : j < 5)
    (hk : k < 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    cj x ℓ₀ i * cj x ℓ₀ j ≠ cj x ℓ₀ k ∧ cj x ℓ₀ i * cj x ℓ₀ j ≠ cj x ℓ₀ k * z := by
  have key : ∀ w : G, (w = 1 ∨ w = z) → cj x ℓ₀ i * cj x ℓ₀ j * cj x ℓ₀ k = w → False := by
    intro w hw htri
    letI : CommGroup ↥E :=
      { (inferInstance : Group ↥E) with mul_comm := fun a b => Subtype.ext (h.comm a a.2 b b.2) }
    let c : ℕ → ↥E := fun r => ⟨cj x ℓ₀ r, h.mem r⟩
    obtain ⟨p, q, hp5, hq5, hpq, hprod⟩ := prod_complement c hi hj hk hij hjk hik
    have hprodG : cj x ℓ₀ i * cj x ℓ₀ j * cj x ℓ₀ k * (cj x ℓ₀ p * cj x ℓ₀ q) =
        cj x ℓ₀ 0 * cj x ℓ₀ 1 * cj x ℓ₀ 2 * cj x ℓ₀ 3 * cj x ℓ₀ 4 := congrArg Subtype.val hprod
    rw [htri] at hprodG
    have hz2 := h.z_sq
    have hne := h.mul_ne hp5 hq5 hpq
    rcases h.prod_mem with hP | hP
    · rw [hP] at hprodG
      rcases hw with hw | hw
      · rw [hw, one_mul] at hprodG
        exact hne.1 hprodG
      · rw [hw] at hprodG
        apply hne.2
        rw [eq_inv_of_mul_eq_one_right hprodG]
        exact inv_eq_of_mul_eq_one_right hz2
    · rw [hP] at hprodG
      rcases hw with hw | hw
      · rw [hw, one_mul] at hprodG
        exact hne.2 hprodG
      · rw [hw] at hprodG
        apply hne.1
        exact mul_left_cancel (a := z) (by rw [hprodG, mul_one])
  refine ⟨fun h1 => key 1 (Or.inl rfl) ?_, fun h1 => key z (Or.inr rfl) ?_⟩
  · rw [h1, h.sq_cj k]
  · rw [h1, h.comm _ (h.mem k) _ h.z_mem, mul_assoc, h.sq_cj k, mul_one]

end Five

end CFSG.LocalAnalysis.EvenBN.Tits.N.PZ
