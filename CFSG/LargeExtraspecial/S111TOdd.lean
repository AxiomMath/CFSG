module

public import CFSG.GroupTheory.PCore.Defs
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LargeExtraspecial.S11

open Subgroup

variable {H : Type*} [Group H]

theorem eq_one_of_pow_two_pow_of_odd {a : H} {m n : ℕ} (ha : a ^ (2 ^ n) = 1) (hm : Odd m)
    (ham : a ^ m = 1) : a = 1 := by
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hm)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha)
    (orderOf_dvd_of_pow_eq_one ham))

variable [Finite H]

theorem le_of_oddCore_eq_bot {Y N R : Subgroup H} (hNR : N ≤ R) (hRY : R ≤ Y)
    (hYN : Y ≤ centralizer (N : Set H)) (hN2 : IsPGroup 2 N)
    (hRn : ∀ y ∈ Y, ∀ r ∈ R, y * r * y⁻¹ ∈ R) {m : ℕ} (hm : Odd m)
    (hcard : Nat.card R = Nat.card N * m) (hO : CFSG.oddCore Y = ⊥) : R ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ r ∈ R, ∀ n ∈ N, r * n = n * r := fun r hr n hn =>
    (mem_centralizer_iff.mp (hYN (hRY hr)) n hn).symm
  set N' := N.subgroupOf R with hN'def
  have hN'n : N'.Normal := ⟨fun n hn r => by
    rw [hN'def, mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcomm _ r.2 _ hn, mul_inv_cancel_right]
    exact hn⟩
  have hN'card : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
  have hN'index : N'.index = m := by
    have h1 := N'.card_mul_index
    rw [hN'card, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  obtain ⟨a, ha⟩ := hN2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card N') N'.index := by
    rw [hN'card, ha, hN'index]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  obtain ⟨D', hD'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hD'card : Nat.card D' = m := by
    have h1 := hD'.card_mul_card
    rw [hN'card, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hoddmem : ∀ x : R, Odd (orderOf x) → x ∈ D' := by
    intro x hx
    obtain ⟨⟨n, d⟩, hnd⟩ := hD'.2 x
    change (n : R) * (d : R) = x at hnd
    have hnc : Commute (n : R) (d : R) :=
      Subtype.ext (hcomm _ d.1.2 _ (mem_subgroupOf.mp n.2)).symm
    have hk : ((n : R) ^ orderOf x) * ((d : R) ^ orderOf x) = 1 := by
      rw [← hnc.mul_pow, hnd, pow_orderOf_eq_one]
    have hnk1 : (n : R) ^ orderOf x = 1 := by
      have hdisj := hD'.disjoint
      rw [Subgroup.disjoint_def] at hdisj
      exact hdisj (N'.pow_mem n.2 _) (by
        rw [eq_inv_of_mul_eq_one_left hk]
        exact D'.inv_mem (D'.pow_mem d.2 _))
    obtain ⟨b, hb⟩ := hN2 ⟨((n : R) : H), mem_subgroupOf.mp n.2⟩
    have hnb : (n : R) ^ (2 ^ b) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hb
      simpa using this
    have hn1 : (n : R) = 1 := eq_one_of_pow_two_pow_of_odd hnb hx hnk1
    rw [← hnd, hn1, one_mul]
    exact d.2
  set D := D'.map R.subtype with hDdef
  have hDcard : Nat.card D = m := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hD'card]
  have hDY : D ≤ Y := (map_subtype_le _).trans hRY
  have hDn : ∀ y ∈ Y, ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    rintro y hy _ ⟨d, hd, rfl⟩
    have hdR : y * (d : H) * y⁻¹ ∈ R := hRn y hy _ d.2
    refine ⟨⟨y * (d : H) * y⁻¹, hdR⟩, hoddmem _ ?_, rfl⟩
    have hord : orderOf (⟨y * (d : H) * y⁻¹, hdR⟩ : R) = orderOf d := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe d]
      change orderOf (y * (d : H) * y⁻¹) = orderOf (d : H)
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [hord]
    exact (hD'card ▸ hm).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hd)
  have hDN : (D.subgroupOf Y).Normal := ⟨fun d hd y => by
    rw [mem_subgroupOf] at hd ⊢
    exact hDn y y.2 d hd⟩
  have hDcard' : Nat.card (D.subgroupOf Y) = m := by
    rw [← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY).toEquiv
  have hDO : D.subgroupOf Y ≤ CFSG.oddCore Y := le_sSup ⟨hDN, hDcard' ▸ hm⟩
  rw [hO, le_bot_iff] at hDO
  have hm1 : m = 1 := by rw [← hDcard', hDO, Subgroup.card_bot]
  rw [hm1, mul_one] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hNR hcard.le).ge

end CFSG.LargeExtraspecial.S11
