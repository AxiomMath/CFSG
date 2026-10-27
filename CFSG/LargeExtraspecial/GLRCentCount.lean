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

namespace CFSG.LargeExtraspecial.GLR

open Subgroup

theorem factorization_le_of_le_pow {p e m : ℕ} (hp : p.Prime) (hm : m ≠ 0) (h : m ≤ p ^ e) :
    m.factorization p ≤ e :=
  (Nat.pow_le_pow_iff_right hp.one_lt).1 ((Nat.ordProj_le p hm).trans h)

section Group

variable {G : Type*} [Group G] {p e : ℕ}

theorem factorization_card_le_add_of_relIndex_le (hp : p.Prime) {H K : Subgroup G} [Finite K]
    (hidx : H.relIndex K ≤ p ^ e) :
    (Nat.card K).factorization p ≤ e + (Nat.card ↥(H ⊓ K)).factorization p := by
  have hK : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have h := Subgroup.relIndex_mul_card H K
  have h1 : H.relIndex K ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact hK h.symm
  have h2 : Nat.card ↥(H ⊓ K) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact hK h.symm
  rw [← h, Nat.factorization_mul h1 h2, Finsupp.add_apply]
  have := factorization_le_of_le_pow hp h1 hidx
  omega

theorem conj_eq_conj_iff_inv_mul_commute {a b y : G} :
    a * y * a⁻¹ = b * y * b⁻¹ ↔ a⁻¹ * b * y = y * (a⁻¹ * b) := by
  constructor
  · intro h
    calc a⁻¹ * b * y = a⁻¹ * (b * y * b⁻¹) * b := by group
      _ = a⁻¹ * (a * y * a⁻¹) * b := by rw [h]
      _ = y * (a⁻¹ * b) := by group
  · intro h
    calc a * y * a⁻¹ = a * (y * (a⁻¹ * b)) * b⁻¹ := by group
      _ = a * (a⁻¹ * b * y) * b⁻¹ := by rw [h]
      _ = b * y * b⁻¹ := by group

theorem relIndex_centralizer_le_ncard {K : Subgroup G} {y : G} {S : Set G} (hSf : S.Finite)
    (hS : ∀ k ∈ K, k * y * k⁻¹ ∈ S) : (centralizer {y}).relIndex K ≤ S.ncard := by
  classical
  have : Finite S := hSf
  have key : ∀ a b : K, a⁻¹ * b ∈ (centralizer {y}).subgroupOf K ↔
      (a : G) * y * (a : G)⁻¹ = (b : G) * y * (b : G)⁻¹ := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      conj_eq_conj_iff_inv_mul_commute]
    simp
  let f : K ⧸ (centralizer {y}).subgroupOf K → S :=
    Quotient.lift (fun k : K => (⟨(k : G) * y * (k : G)⁻¹, hS k k.2⟩ : S)) (fun a b hab =>
      Subtype.ext ((key a b).1 (QuotientGroup.leftRel_apply.mp hab)))
  have hf : Function.Injective f := by
    rintro ⟨a⟩ ⟨b⟩ hab
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((key a b).2 (congrArg Subtype.val hab)))
  rw [Subgroup.relIndex, Subgroup.index, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective f hf

theorem factorization_card_le_add_centralizer (hp : p.Prime) {K : Subgroup G} [Finite K]
    {y : G} {S : Set G} (hSf : S.Finite) (hS : ∀ k ∈ K, k * y * k⁻¹ ∈ S)
    (hcard : S.ncard ≤ p ^ e) :
    (Nat.card K).factorization p ≤ e + (Nat.card ↥(K ⊓ centralizer {y})).factorization p := by
  have := factorization_card_le_add_of_relIndex_le hp
    ((relIndex_centralizer_le_ncard hSf hS).trans hcard)
  rwa [inf_comm] at this

end Group

theorem mul_pred_div_two_mul_two (n : ℕ) : n * (n - 1) / 2 * 2 = n * (n - 1) :=
  Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)

theorem centExp_add_choose {n k : ℕ} (h : 2 * k ≤ n) :
    k * (2 * n - 3 * k) + k * (k - 1) / 2 + (n - 2 * k) * (n - 2 * k - 1) / 2 + k * (k - 1) / 2 =
      n * (n - 1) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * k + m := ⟨n - 2 * k, by omega⟩
  have e1 : 2 * (2 * k + m) - 3 * k = k + 2 * m := by omega
  have e2 : 2 * k + m - 2 * k = m := by omega
  rw [e1, e2]
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
  rw [add_mul, add_mul, add_mul, mul_pred_div_two_mul_two, mul_pred_div_two_mul_two,
    mul_pred_div_two_mul_two, Nat.mul_sub_one, Nat.mul_sub_one, Nat.mul_sub_one]
  have h1 := Nat.le_mul_self k
  have h2 := Nat.le_mul_self m
  have h3 := Nat.le_mul_self (2 * k + m)
  zify [h1, h2, h3]
  ring

theorem centExp_lt_of_add_eq {N r v : ℕ} (hN : 5 ≤ N) (hr : 1 ≤ r) (hrN : 2 * r ≤ N)
    (hv : v + r * (r - 1) / 2 = N * (N - 1) / 2) :
    2 + 2 * ((N - 1) / 2) + ((N - 1) / 2) ^ 2 < r + v := by
  have ha := mul_pred_div_two_mul_two r
  have hs := mul_pred_div_two_mul_two N
  set a := r * (r - 1) / 2
  set s := N * (N - 1) / 2
  obtain ⟨M, hM | hM⟩ : ∃ M, N = 2 * M + 1 ∨ N = 2 * M + 2 := ⟨(N - 1) / 2, by omega⟩
  · have hM' : (N - 1) / 2 = M := by omega
    rw [hM']
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    subst hM
    have e1 : 2 * M + 1 - 1 = 2 * M := by omega
    rw [e1] at hs
    rw [Nat.add_sub_cancel] at ha
    have hrM : r' + 1 ≤ M := by omega
    have hM2 : 2 ≤ M := by omega
    nlinarith
  · have hM' : (N - 1) / 2 = M := by omega
    rw [hM']
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    subst hM
    have e1 : 2 * M + 2 - 1 = 2 * M + 1 := by omega
    rw [e1] at hs
    rw [Nat.add_sub_cancel] at ha
    have hrM : r' ≤ M := by omega
    have hM2 : 2 ≤ M := by omega
    nlinarith

end CFSG.LargeExtraspecial.GLR
