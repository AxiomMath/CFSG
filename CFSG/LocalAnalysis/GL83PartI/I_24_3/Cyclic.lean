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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace GL83.I243

open Finset

theorem card_pow_pow_eq_one_le {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] {p : ℕ}
    (h : #{x : G | x ^ p = 1} ≤ p) (k : ℕ) : #{x : G | x ^ (p ^ k) = 1} ≤ p ^ k := by
  induction k with
  | zero =>
    have : #{x : G | x ^ (p ^ 0) = 1} ≤ #({1} : Finset G) := by
      refine Finset.card_le_card ?_
      intro x hx
      simpa using hx
    simpa using this
  | succ k ih =>
    set S : Finset G := {x : G | x ^ (p ^ (k + 1)) = 1} with hS
    have hmaps : ∀ x ∈ S, x ^ p ∈ ({x : G | x ^ (p ^ k) = 1} : Finset G) := by
      intro x hx
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [← pow_mul, ← pow_succ']
      exact hx
    have himg : S.image (fun x => x ^ p) ⊆ ({x : G | x ^ (p ^ k) = 1} : Finset G) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact hmaps x hx
    have hfib : ∀ a ∈ S.image (fun x => x ^ p), #{x ∈ S | x ^ p = a} ≤ p := by
      intro a ha
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp ha
      refine le_trans ?_ h
      refine Finset.card_le_card_of_injOn (fun x => x * x₀⁻¹) ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [mul_pow, inv_pow, hx.2, mul_inv_cancel]
      · intro x _ y _ hxy
        exact mul_right_cancel hxy
    have := Finset.card_le_mul_card_image S p hfib
    calc #S ≤ p * #(S.image (fun x => x ^ p)) := this
      _ ≤ p * #{x : G | x ^ (p ^ k) = 1} := Nat.mul_le_mul_left _ (Finset.card_le_card himg)
      _ ≤ p * p ^ k := Nat.mul_le_mul_left _ ih
      _ = p ^ (k + 1) := by ring

theorem isCyclic_of_isPGroup_of_card_pow_le {G : Type*} [CommGroup G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hG : IsPGroup p G) (h : Nat.card {x : G // x ^ p = 1} ≤ p) : IsCyclic G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have h' : #{x : G | x ^ p = 1} ≤ p := by
    have : Nat.card {x : G // x ^ p = 1} = #{x : G | x ^ p = 1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    omega
  refine isCyclic_of_card_pow_eq_one_le ?_
  intro n hn
  obtain ⟨e, m, hm0, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
  have : Fact p.Prime := ⟨hp⟩
  have hsub : (Finset.univ.filter fun x : G => x ^ n = 1) ⊆
      (Finset.univ.filter fun x : G => x ^ (p ^ e) = 1) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hG) x
    have hdvd : orderOf x ∣ p ^ e * m := hmn ▸ orderOf_dvd_of_pow_eq_one hx
    have hcop : Nat.Coprime (orderOf x) m := by
      rw [ha]
      exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm0)
    have : orderOf x ∣ p ^ e := hcop.dvd_of_dvd_mul_right hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0] at hmn; omega
    · exact h0
  calc #(Finset.univ.filter fun x : G => x ^ n = 1) ≤
      #(Finset.univ.filter fun x : G => x ^ (p ^ e) = 1) := Finset.card_le_card hsub
    _ ≤ p ^ e := card_pow_pow_eq_one_le h' e
    _ ≤ n := by rw [hmn]; exact Nat.le_mul_of_pos_right _ hm1

end GL83.I243
