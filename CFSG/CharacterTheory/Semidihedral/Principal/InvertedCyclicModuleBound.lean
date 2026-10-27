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
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

open Polynomial

namespace CFSG.Semidihedral.Principal

variable {L : Type*} [Field L]

theorem iterate_pow_apply (p : ℕ) (x : L) (j : ℕ) :
    (fun y : L => y ^ p)^[j] x = x ^ p ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, ← pow_mul, pow_succ]

theorem even_orderOf_of_pow_eq_neg_one (h2 : ringChar L ≠ 2) {N : ℕ} {y : L}
    (hy : y ^ N = -1) : Even (orderOf y) := by
  have hy1 : y ^ N ≠ 1 := by
    rw [hy]
    exact Ring.neg_one_ne_one_of_char_ne_two h2
  have hdvd : orderOf y ∣ 2 * N := orderOf_dvd_of_pow_eq_one (by
    rw [mul_comm, pow_mul, hy, neg_one_sq])
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  exact hy1 (orderOf_dvd_iff_pow_eq_one.mp
    ((Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd)) hdvd))

theorem exists_frobenius_inversion_orbit [Finite L] [DecidableEq L] {p : ℕ} [hp : Fact p.Prime]
    [CharP L p] (h2 : ringChar L ≠ 2) {Λ : Finset L} (hφ : ∀ y ∈ Λ, y ^ p ∈ Λ)
    (hι : ∀ y ∈ Λ, y⁻¹ ∈ Λ) {N : ℕ} (hN : ∀ y ∈ Λ, y ^ N = -1) {x : L} (hx : x ∈ Λ)
    (hx1 : x ≠ -1) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ O : Finset L, O ⊆ Λ ∧ x ∈ O ∧ O.card = 2 * a ∧
      (∀ y ∈ Λ \ O, y ^ p ∈ Λ \ O) ∧ (∀ y ∈ Λ \ O, y⁻¹ ∈ Λ \ O) ∧
      O.lcm orderOf = orderOf x ∧ orderOf x ≤ p ^ a + 1 ∧
      (orderOf x + 1 ≤ p ^ a ∨ ∀ y ∈ O, ∃ j, y = x ^ p ^ j) := by
  have := Fintype.ofFinite L
  have hp2 : 2 ≤ p := hp.out.two_le
  have hneg : (-1 : L) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two h2
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hneg (by rw [← hN x hx, pow_zero])
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h := hN 0 hx
    rw [zero_pow hN0] at h
    exact one_ne_zero (neg_eq_zero.mp h.symm)
  have hxx : x⁻¹ ≠ x := by
    intro h
    have : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel₀ hx0
    rcases mul_self_eq_one_iff.mp this with h1 | h1
    · exact hneg (by rw [← hN x hx, h1, one_pow])
    · exact hx1 h1
  obtain ⟨e, -, hcard⟩ := FiniteField.card L p
  have hper : Function.IsPeriodicPt (fun y : L => y ^ p) e x := by
    change (fun y : L => y ^ p)^[e] x = x
    rw [iterate_pow_apply, ← hcard, FiniteField.pow_card]
  set b := Function.minimalPeriod (fun y : L => y ^ p) x with hb
  have hb0 : 0 < b := hper.minimalPeriod_pos e.pos
  have hxb : x ^ p ^ b = x := by
    rw [← iterate_pow_apply]
    exact Function.iterate_minimalPeriod
  have hmod : ∀ j, x ^ p ^ j = x ^ p ^ (j % b) := by
    intro j
    rw [← iterate_pow_apply, ← iterate_pow_apply, hb, Function.iterate_mod_minimalPeriod_eq]
  set F := (Finset.range b).image fun j => x ^ p ^ j with hF
  have hFmem : ∀ j, x ^ p ^ j ∈ F := by
    intro j
    rw [hmod j]
    exact Finset.mem_image.mpr ⟨j % b, Finset.mem_range.mpr (Nat.mod_lt j hb0), rfl⟩
  have hFcard : F.card = b := by
    rw [hF, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := fun y : L => y ^ p) (x := x)
    exact hinj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (by simp only [iterate_pow_apply]; exact hij)
  have hΛpow : ∀ j, x ^ p ^ j ∈ Λ := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih => rw [pow_succ, pow_mul]; exact hφ _ ih
  have hm : ∀ j, (x ^ p ^ j) ^ orderOf x = 1 := by
    intro j
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hFφ : ∀ y ∈ F, y ^ p ∈ F := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← pow_mul, ← pow_succ]
    exact hFmem (j + 1)
  have hFΛ : F ⊆ Λ := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    exact hΛpow j
  have hinj : Function.Injective (fun y : L => y ^ p) := by
    have : ExpChar L p := ExpChar.prime hp.out
    exact frobenius_inj L p
  have hclosed : ∀ O : Finset L, O ⊆ Λ → (∀ y ∈ O, y ^ p ∈ O) → (∀ y ∈ O, y⁻¹ ∈ O) →
      (∀ y ∈ Λ \ O, y ^ p ∈ Λ \ O) ∧ (∀ y ∈ Λ \ O, y⁻¹ ∈ Λ \ O) := by
    intro O hOΛ hOφ hOι
    have himage : O.image (fun y : L => y ^ p) = O :=
      Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hOφ)
        (by rw [Finset.card_image_of_injective _ hinj])
    constructor
    · intro y hy
      obtain ⟨hyΛ, hyO⟩ := Finset.mem_sdiff.mp hy
      refine Finset.mem_sdiff.mpr ⟨hφ y hyΛ, fun h => hyO ?_⟩
      rw [← himage] at h
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp h
      rwa [← hinj hzy]
    · intro y hy
      obtain ⟨hyΛ, hyO⟩ := Finset.mem_sdiff.mp hy
      refine Finset.mem_sdiff.mpr ⟨hι y hyΛ, fun h => hyO ?_⟩
      simpa using hOι _ h
  have hlcm : ∀ O : Finset L, x ∈ O → (∀ y ∈ O, y ^ orderOf x = 1) →
      O.lcm orderOf = orderOf x := by
    intro O hxO hO
    apply Nat.dvd_antisymm
    · exact Finset.lcm_dvd_iff.mpr fun y hy => orderOf_dvd_of_pow_eq_one (hO y hy)
    · exact Finset.dvd_lcm hxO
  have hxF : x ∈ F := by simpa using hFmem 0
  by_cases hcase : x⁻¹ ∈ F
  · obtain ⟨j, hj, hxj⟩ := Finset.mem_image.mp hcase
    rw [Finset.mem_range] at hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hxx (by rw [← hxj, pow_zero, pow_one])
    have h2j : x ^ p ^ (2 * j) = x := by
      rw [two_mul, pow_add, pow_mul, hxj, inv_pow, hxj, inv_inv]
    have hbj : b = 2 * j := by
      have hdvd : b ∣ 2 * j := by
        rw [hb, ← Function.isPeriodicPt_iff_minimalPeriod_dvd]
        change (fun y : L => y ^ p)^[2 * j] x = x
        rw [iterate_pow_apply, h2j]
      exact (Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd (by omega)).symm
    have hFι : ∀ y ∈ F, y⁻¹ ∈ F := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [← inv_pow, ← hxj, ← pow_mul, ← pow_add]
      exact hFmem (j + i)
    obtain ⟨hc1, hc2⟩ := hclosed F hFΛ hFφ hFι
    refine ⟨j, by omega, F, hFΛ, hxF, by rw [hFcard, hbj], hc1, hc2,
      hlcm F hxF ?_, ?_, Or.inr ?_⟩
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact hm i
    · apply orderOf_le_of_pow_eq_one (by positivity)
      rw [pow_succ, hxj, inv_mul_cancel₀ hx0]
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨i, rfl⟩
  · set O := F ∪ F.image (·⁻¹) with hO
    have hdisj : Disjoint F (F.image (·⁻¹)) := by
      rw [Finset.disjoint_left]
      intro y hyF hyI
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hyF
      obtain ⟨z, hzF, hz⟩ := Finset.mem_image.mp hyI
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hzF
      rw [Finset.mem_range] at hl
      apply hcase
      have : x⁻¹ = x ^ p ^ (i + (b - l)) := by
        calc x⁻¹ = (x ^ p ^ b)⁻¹ := by rw [hxb]
          _ = ((x ^ p ^ l)⁻¹) ^ p ^ (b - l) := by
              rw [inv_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hl.le]
          _ = x ^ p ^ (i + (b - l)) := by rw [hz, ← pow_mul, ← pow_add]
      rw [this]
      exact hFmem _
    have hOcard : O.card = 2 * b := by
      rw [hO, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ inv_injective, hFcard, two_mul]
    have hOφ : ∀ y ∈ O, y ^ p ∈ O := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_union_left _ (hFφ y hy)
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z ^ p, hFφ z hz, by rw [inv_pow]⟩)
    have hOι : ∀ y ∈ O, y⁻¹ ∈ O := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        rw [inv_inv]
        exact Finset.mem_union_left _ hz
    have hOΛ : O ⊆ Λ := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact hFΛ hy
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        exact hι z (hFΛ hz)
    obtain ⟨hc1, hc2⟩ := hclosed O hOΛ hOφ hOι
    have hxO : x ∈ O := Finset.mem_union_left _ hxF
    have hpb : 2 ≤ p ^ b := le_trans hp2 (Nat.le_self_pow hb0.ne' p)
    have hord : orderOf x + 1 ≤ p ^ b := by
      have : orderOf x ≤ p ^ b - 1 := by
        apply orderOf_le_of_pow_eq_one (by omega)
        have h := hxb
        rw [← pow_sub_one_mul (by omega : p ^ b ≠ 0)] at h
        exact mul_eq_right₀ hx0 |>.mp h
      omega
    refine ⟨b, hb0, O, hOΛ, hxO, hOcard, hc1, hc2, hlcm O hxO ?_, by omega, Or.inl hord⟩
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact hm i
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      rw [inv_pow, hm i, inv_one]

theorem lcm_le_pow_add_one_of_even {p a c m l : ℕ} (hp : 2 ≤ p) (hm : Even m) (hl : Even l)
    (hl0 : 0 < l) (hma : m ≤ p ^ a + 1) (hlc : l ≤ p ^ c + 1) :
    Nat.lcm m l ≤ p ^ (a + c) + 1 ∧ (1 ≤ a → 1 ≤ c → Nat.lcm m l < p ^ (a + c) + 1) := by
  have hgcd : 2 ≤ Nat.gcd m l :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_right m hl0) (Nat.dvd_gcd hm.two_dvd hl.two_dvd)
  have h2lcm : 2 * Nat.lcm m l ≤ m * l := by
    rw [← Nat.gcd_mul_lcm m l]
    exact Nat.mul_le_mul_right _ hgcd
  have hml : m * l ≤ (p ^ a + 1) * (p ^ c + 1) := Nat.mul_le_mul hma hlc
  have hP : 1 ≤ p ^ a := Nat.one_le_pow _ _ (by omega)
  have hQ : 1 ≤ p ^ c := Nat.one_le_pow _ _ (by omega)
  rw [pow_add]
  refine ⟨by nlinarith, fun ha hc => ?_⟩
  have hP2 : 2 ≤ p ^ a := le_trans hp (Nat.le_self_pow (by omega) p)
  have hQ2 : 2 ≤ p ^ c := le_trans hp (Nat.le_self_pow (by omega) p)
  nlinarith

theorem orderOf_pos_of_pow_eq_neg_one (h2 : ringChar L ≠ 2) {N : ℕ} {y : L}
    (hy : y ^ N = -1) : 0 < orderOf y := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact Ring.neg_one_ne_one_of_char_ne_two h2 (by rw [← hy, pow_zero])
  exact IsOfFinOrder.orderOf_pos (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * N, by omega, by
    rw [mul_comm, pow_mul, hy, neg_one_sq]⟩)

theorem lcm_orderOf_le_of_frobenius_inversion_closed [Finite L] [DecidableEq L] {p : ℕ}
    [hp : Fact p.Prime] [CharP L p] (h2 : ringChar L ≠ 2) {N : ℕ} (Λ : Finset L)
    (hφ : ∀ y ∈ Λ, y ^ p ∈ Λ) (hι : ∀ y ∈ Λ, y⁻¹ ∈ Λ) (hN : ∀ y ∈ Λ, y ^ N = -1) :
    Λ.lcm orderOf ≤ p ^ (Λ.card / 2) + 1 := by
  induction Λ using Finset.strongInduction with
  | H Λ ih =>
  have hp2 : 2 ≤ p := hp.out.two_le
  by_cases hall : ∀ y ∈ Λ, y = -1
  · have hdvd : Λ.lcm orderOf ∣ 2 := Finset.lcm_dvd_iff.mpr fun y hy => by
      rw [hall y hy, orderOf_neg_one]
      simp [h2]
    have := Nat.le_of_dvd two_pos hdvd
    have : 1 ≤ p ^ (Λ.card / 2) := Nat.one_le_pow _ _ (by omega)
    omega
  push Not at hall
  obtain ⟨x, hx, hx1⟩ := hall
  obtain ⟨a, ha1, O, hOΛ, hxO, hOcard, hc1, hc2, hOlcm, hma, -⟩ :=
    exists_frobenius_inversion_orbit h2 hφ hι hN hx hx1
  have hN' : ∀ y ∈ Λ \ O, y ^ N = -1 := fun y hy => hN y (Finset.mem_sdiff.mp hy).1
  have ih' := ih (Λ \ O) (Finset.sdiff_ssubset hOΛ ⟨x, hxO⟩) hc1 hc2 hN'
  have hcardΛ : Λ.card = 2 * a + (Λ \ O).card := by
    rw [← hOcard, ← Finset.card_sdiff_add_card_eq_card hOΛ, add_comm]
  have hlcmΛ : Λ.lcm orderOf = Nat.lcm (orderOf x) ((Λ \ O).lcm orderOf) := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset hOΛ]
    rw [Finset.lcm_union, hOlcm]
    rfl
  have hm := even_orderOf_of_pow_eq_neg_one h2 (hN x hx)
  have hl0 : 0 < (Λ \ O).lcm orderOf := Nat.pos_of_ne_zero fun h => by
    obtain ⟨y, hy, hy0⟩ := Finset.lcm_eq_zero_iff.mp h
    exact (orderOf_pos_of_pow_eq_neg_one h2 (hN' y hy)).ne' hy0
  rw [hlcmΛ]
  by_cases hl2 : (Λ \ O).lcm orderOf ≤ 2
  · have hdvd : (Λ \ O).lcm orderOf ∣ orderOf x := by
      interval_cases h : (Λ \ O).lcm orderOf
      · exact one_dvd _
      · exact hm.two_dvd
    rw [Nat.lcm_eq_left hdvd]
    exact le_trans hma (by gcongr; omega)
  · obtain ⟨y, hy⟩ : (Λ \ O).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.lcm_empty] at hl2
      omega
    have hl : Even ((Λ \ O).lcm orderOf) :=
      even_iff_two_dvd.mpr ((even_orderOf_of_pow_eq_neg_one h2 (hN' y hy)).two_dvd.trans
        (Finset.dvd_lcm hy))
    have := (lcm_le_pow_add_one_of_even hp2 hm hl hl0 hma ih').1
    exact le_trans this (by gcongr; omega)

theorem exists_frobenius_orbit_of_lcm_orderOf_eq [Finite L] [DecidableEq L] {p : ℕ}
    [hp : Fact p.Prime] [CharP L p] (h2 : ringChar L ≠ 2) {N : ℕ} {Λ : Finset L}
    (hφ : ∀ y ∈ Λ, y ^ p ∈ Λ) (hι : ∀ y ∈ Λ, y⁻¹ ∈ Λ) (hN : ∀ y ∈ Λ, y ^ N = -1) {f : ℕ}
    (hf : 1 ≤ f) (hcard : Λ.card ≤ 2 * f) (hlcm : Λ.lcm orderOf = p ^ f + 1) :
    Λ.card = 2 * f ∧ ∃ x ∈ Λ, ∀ y ∈ Λ, ∃ j, y = x ^ p ^ j := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hB := lcm_orderOf_le_of_frobenius_inversion_closed h2 Λ hφ hι hN
  rw [hlcm] at hB
  have hpow : p ^ f ≤ p ^ (Λ.card / 2) := by omega
  have hf' : f ≤ Λ.card / 2 := (Nat.pow_le_pow_iff_right (by omega)).mp hpow
  have hcard' : Λ.card = 2 * f := by omega
  refine ⟨hcard', ?_⟩
  have hpf : 2 ≤ p ^ f := le_trans hp2 (Nat.le_self_pow (by omega) p)
  by_cases hall : ∀ y ∈ Λ, y = -1
  · have hdvd : Λ.lcm orderOf ∣ 2 := Finset.lcm_dvd_iff.mpr fun y hy => by
      rw [hall y hy, orderOf_neg_one]
      simp [h2]
    have := Nat.le_of_dvd two_pos hdvd
    omega
  push Not at hall
  obtain ⟨x, hx, hx1⟩ := hall
  obtain ⟨a, ha1, O, hOΛ, hxO, hOcard, hc1, hc2, hOlcm, hma, hcase⟩ :=
    exists_frobenius_inversion_orbit h2 hφ hι hN hx hx1
  have hN' : ∀ y ∈ Λ \ O, y ^ N = -1 := fun y hy => hN y (Finset.mem_sdiff.mp hy).1
  have ih' := lcm_orderOf_le_of_frobenius_inversion_closed h2 (Λ \ O) hc1 hc2 hN'
  have hcardΛ : Λ.card = 2 * a + (Λ \ O).card := by
    rw [← hOcard, ← Finset.card_sdiff_add_card_eq_card hOΛ, add_comm]
  have hlcmΛ : Λ.lcm orderOf = Nat.lcm (orderOf x) ((Λ \ O).lcm orderOf) := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset hOΛ]
    rw [Finset.lcm_union, hOlcm]
    rfl
  have hm := even_orderOf_of_pow_eq_neg_one h2 (hN x hx)
  have hrest : Λ \ O = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hl0 : 0 < (Λ \ O).lcm orderOf := Nat.pos_of_ne_zero fun h => by
      obtain ⟨z, hz, hz0⟩ := Finset.lcm_eq_zero_iff.mp h
      exact (orderOf_pos_of_pow_eq_neg_one h2 (hN' z hz)).ne' hz0
    have hrestcard : 1 ≤ (Λ \ O).card := Finset.card_pos.mpr ⟨y, hy⟩
    by_cases hl2 : (Λ \ O).lcm orderOf ≤ 2
    · have hdvd : (Λ \ O).lcm orderOf ∣ orderOf x := by
        interval_cases h : (Λ \ O).lcm orderOf
        · exact one_dvd _
        · exact hm.two_dvd
      rw [hlcmΛ, Nat.lcm_eq_left hdvd] at hlcm
      have : p ^ a < p ^ f := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    · have hl : Even ((Λ \ O).lcm orderOf) :=
        even_iff_two_dvd.mpr ((even_orderOf_of_pow_eq_neg_one h2 (hN' y hy)).two_dvd.trans
          (Finset.dvd_lcm hy))
      have hc : 1 ≤ (Λ \ O).card / 2 := by
        by_contra hc
        have : (Λ \ O).card / 2 = 0 := by omega
        rw [this, pow_zero] at ih'
        omega
      have := (lcm_le_pow_add_one_of_even hp2 hm hl hl0 hma ih').2 ha1 hc
      rw [← hlcmΛ, hlcm] at this
      have : p ^ (a + (Λ \ O).card / 2) ≤ p ^ f := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  have hOeq : O = Λ := by
    apply Finset.Subset.antisymm hOΛ
    intro y hy
    by_contra hyO
    have : y ∈ Λ \ O := Finset.mem_sdiff.mpr ⟨hy, hyO⟩
    rw [hrest] at this
    exact Finset.notMem_empty y this
  have ha : a = f := by
    rw [hOeq] at hOcard
    omega
  rw [hOeq] at hOlcm
  rcases hcase with hlt | hall
  · rw [← hOlcm, hlcm, ha] at hlt
    omega
  · exact ⟨x, hx, fun y hy => hall y (hOeq ▸ hy)⟩

theorem aeval_pow_char_eq_zero {k : Type*} [Field k] [Fintype k] {p : ℕ} (hk : Fintype.card k = p)
    {K : Type*} [Field K] [Algebra k K] {g : k[X]} {z : K} (hz : aeval z g = 0) :
    aeval (z ^ p) g = 0 := by
  rw [← expand_aeval, ← hk, FiniteField.Polynomial.expand_card, map_pow, hz,
    zero_pow Fintype.card_ne_zero]

theorem aeval_pow_char_pow_eq_zero {k : Type*} [Field k] [Fintype k] {p : ℕ}
    (hk : Fintype.card k = p) {K : Type*} [Field K] [Algebra k K] {g : k[X]} {z : K}
    (hz : aeval z g = 0) (j : ℕ) : aeval (z ^ p ^ j) g = 0 := by
  induction j with
  | zero => simpa using hz
  | succ j ih => rw [pow_succ, pow_mul]; exact aeval_pow_char_eq_zero hk ih

theorem aeval_restrict_apply {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (T : Module.End k V) {S : Submodule k V} (hS : ∀ v ∈ S, T v ∈ S) (q : k[X]) (v : S) :
    ((aeval (T.restrict hS) q) v : V) = aeval T q v := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, h₁, h₂]
  | monomial m c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.End.pow_restrict m hS, LinearMap.restrict_apply, Submodule.coe_smul]

theorem inverted_cyclic_prime_field_module_even_order_bound {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) {k : Type*} [Field k] [Fintype k] (hk : Nat.card k = p)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hd : 0 < Module.finrank k V) (A B : LinearMap.GeneralLinearGroup k V) {n : ℕ}
    (hn : orderOf A = n) (heven : Even n) (hpn : ¬ p ∣ n) (hA : A ^ (n / 2) = -1)
    (hB : B * A * B⁻¹ = A⁻¹) :
    n ≤ p ^ (Module.finrank k V / 2) + 1 ∧
      ∀ f : ℕ, 1 ≤ f → Module.finrank k V = 2 * f → n = p ^ f + 1 →
        Irreducible (LinearMap.charpoly (A : V →ₗ[k] V)) ∧
          Representation.IsIrreducible
            ((Units.coeHom (V →ₗ[k] V)).comp (Subgroup.zpowers A).subtype) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcardk : Fintype.card k = p := by rw [← Nat.card_eq_fintype_card]; exact hk
  have : CharP k p := charP_of_card_eq_prime hcardk
  set T : Module.End k V := (A : Module.End k V) with hT
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hpn (dvd_zero p)
  have hTn : T ^ n = 1 := by
    rw [hT, ← Units.val_pow_eq_pow_val, ← hn, pow_orderOf_eq_one, Units.val_one]
  have hint : IsIntegral k T := Algebra.IsIntegral.isIntegral T
  set μ := minpoly k T with hμ
  have hμmonic : μ.Monic := minpoly.monic hint
  have hdvdpow : ∀ m, T ^ m = 1 → μ ∣ X ^ m - 1 := fun m hm =>
    minpoly.dvd k T (by simp [hm])
  have hnk : (n : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
  have hsepXn : (X ^ n - 1 : k[X]).Separable := by
    simpa using separable_X_pow_sub_C (1 : k) hnk one_ne_zero
  have hμsep : μ.Separable := hsepXn.of_dvd (hdvdpow n hTn)
  let L := SplittingField μ
  have hsplit : (μ.map (algebraMap k L)).Splits := SplittingField.splits μ
  have : Finite L := Module.finite_of_finite k
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  have h2L : ringChar L ≠ 2 := by
    rw [ringChar.eq L p]
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) even_two
  set Λ : Finset L := (μ.map (algebraMap k L)).roots.toFinset with hΛ
  have hmap0 : μ.map (algebraMap k L) ≠ 0 := (hμmonic.map _).ne_zero
  have hmemΛ : ∀ y : L, y ∈ Λ ↔ aeval y μ = 0 := by
    intro y
    rw [hΛ, Multiset.mem_toFinset, mem_roots hmap0, IsRoot.def, eval_map_algebraMap]
  have hroot_pow : ∀ m, T ^ m = 1 → ∀ y ∈ Λ, y ^ m = 1 := by
    intro m hm y hy
    obtain ⟨r, hr⟩ := hdvdpow m hm
    have : aeval y (X ^ m - 1 : k[X]) = 0 := by rw [hr, map_mul, (hmemΛ y).mp hy, zero_mul]
    simpa [sub_eq_zero] using this
  have hpow_root : ∀ m, (∀ y ∈ Λ, y ^ m = 1) → T ^ m = 1 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact pow_zero T
    have hq0 : (X ^ m - 1 : k[X]).map (algebraMap k L) ≠ 0 := by
      rw [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
      exact (monic_X_pow_sub_C (1 : L) hm0.ne').ne_zero |> fun h => by simpa using h
    have hle : (μ.map (algebraMap k L)).roots ≤
        ((X ^ m - 1 : k[X]).map (algebraMap k L)).roots := by
      rw [Multiset.le_iff_subset (nodup_roots hμsep.map)]
      intro y hy
      rw [mem_roots hq0, IsRoot.def, eval_map_algebraMap]
      have := hm y (by rw [hΛ, Multiset.mem_toFinset]; exact hy)
      simp [this]
    have hdvd : μ.map (algebraMap k L) ∣ (X ^ m - 1 : k[X]).map (algebraMap k L) := by
      rw [hsplit.eq_prod_roots_of_monic (hμmonic.map _)]
      exact (Multiset.prod_X_sub_C_dvd_iff_le_roots hq0 _).mpr hle
    obtain ⟨r, hr⟩ := (map_dvd_map _ (algebraMap k L).injective hμmonic).mp hdvd
    have : aeval T (X ^ m - 1 : k[X]) = 0 := by rw [hr, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using this
  have horder : orderOf A = Λ.lcm orderOf := by
    rw [← orderOf_units]
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      apply hpow_root
      intro y hy
      exact orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_lcm hy)
    · apply Finset.lcm_dvd_iff.mpr
      intro y hy
      exact orderOf_dvd_of_pow_eq_one (hroot_pow _ (pow_orderOf_eq_one T) y hy)
  have hφ : ∀ y ∈ Λ, y ^ p ∈ Λ := fun y hy =>
    (hmemΛ _).mpr (aeval_pow_char_eq_zero hcardk ((hmemΛ y).mp hy))
  have hAinv : ((A⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) = T ^ (n - 1) := by
    rw [hT, ← Units.val_pow_eq_pow_val]
    congr 1
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel (by omega), ← hn, pow_orderOf_eq_one]
  have hconj : ((A⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
      B.toLinearEquiv.conjAlgEquiv k T := by
    rw [← hB]
    rfl
  have hinv0 : aeval (T ^ (n - 1)) μ = 0 := by
    rw [← hAinv, hconj, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hcomp : μ ∣ μ.comp (X ^ (n - 1)) := minpoly.dvd k T (by
    rw [aeval_comp, aeval_X_pow, hinv0])
  have hι : ∀ y ∈ Λ, y⁻¹ ∈ Λ := by
    intro y hy
    have hyn : y ^ n = 1 := hroot_pow n hTn y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hn0] at hyn
      exact zero_ne_one hyn
    have hinv : y⁻¹ = y ^ (n - 1) := by
      rw [inv_eq_iff_eq_inv, eq_comm]
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hyn]
    obtain ⟨r, hr⟩ := hcomp
    have h := congrArg (aeval y) hr
    rw [aeval_comp, aeval_X_pow, map_mul, (hmemΛ y).mp hy, zero_mul] at h
    rw [hinv]
    exact (hmemΛ _).mpr h
  have hN : ∀ y ∈ Λ, y ^ (n / 2) = -1 := by
    intro y hy
    have hT2 : T ^ (n / 2) = -1 := by
      rw [hT, ← Units.val_pow_eq_pow_val, hA, Units.val_neg, Units.val_one]
    obtain ⟨r, hr⟩ := minpoly.dvd k T (p := X ^ (n / 2) + 1) (by simp [hT2])
    have : aeval y (X ^ (n / 2) + 1 : k[X]) = 0 := by rw [hr, map_mul, (hmemΛ y).mp hy, zero_mul]
    simpa [add_eq_zero_iff_eq_neg] using this
  have hΛcard : Λ.card = μ.natDegree := by
    rw [hΛ, Multiset.toFinset_card_of_nodup (nodup_roots hμsep.map),
      ← hsplit.natDegree_eq_card_roots, natDegree_map]
  have hμdeg : μ.natDegree ≤ Module.finrank k V := by
    rw [← LinearMap.charpoly_natDegree T]
    exact natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly T)
      (LinearMap.charpoly_monic T).ne_zero
  have hbound := lcm_orderOf_le_of_frobenius_inversion_closed h2L Λ hφ hι hN
  refine ⟨?_, ?_⟩
  · rw [← hn, horder]
    exact le_trans hbound (Nat.add_le_add_right (Nat.pow_le_pow_right hp.pos
      (Nat.div_le_div_right (hΛcard ▸ hμdeg))) 1)
  · intro f hf hdf hnf
    have hlcm : Λ.lcm orderOf = p ^ f + 1 := by rw [← horder, hn, hnf]
    obtain ⟨hcardf, x, hx, hxall⟩ := exists_frobenius_orbit_of_lcm_orderOf_eq h2L hφ hι hN hf
      (by rw [hΛcard, ← hdf]; exact hμdeg) hlcm
    have hxint : IsIntegral k x := Algebra.IsIntegral.isIntegral x
    have hxdvd : minpoly k x ∣ μ := minpoly.dvd k x ((hmemΛ x).mp hx)
    have hdeg : μ.natDegree ≤ (minpoly k x).natDegree := by
      have hm0 : (minpoly k x).map (algebraMap k L) ≠ 0 :=
        ((minpoly.monic hxint).map _).ne_zero
      rw [← hΛcard]
      calc Λ.card ≤ ((minpoly k x).map (algebraMap k L)).roots.toFinset.card := by
            apply Finset.card_le_card
            intro y hy
            obtain ⟨j, rfl⟩ := hxall y hy
            rw [Multiset.mem_toFinset, mem_roots hm0, IsRoot.def, eval_map_algebraMap]
            exact aeval_pow_char_pow_eq_zero hcardk (minpoly.aeval k x) j
        _ ≤ ((minpoly k x).map (algebraMap k L)).roots.card := Multiset.toFinset_card_le _
        _ ≤ ((minpoly k x).map (algebraMap k L)).natDegree := card_roots' _
        _ = (minpoly k x).natDegree := natDegree_map _
    have hμeq : μ = minpoly k x :=
      eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxint) hμmonic hxdvd hdeg
    have hμirr : Irreducible μ := hμeq ▸ minpoly.irreducible hxint
    have hμd : μ.natDegree = Module.finrank k V := by rw [← hΛcard, hcardf, hdf]
    have hchar : LinearMap.charpoly T = μ :=
      eq_of_monic_of_dvd_of_natDegree_le hμmonic (LinearMap.charpoly_monic T)
        (LinearMap.minpoly_dvd_charpoly T) (by rw [LinearMap.charpoly_natDegree, hμd])
    refine ⟨by rw [hchar]; exact hμirr, ?_⟩
    have : Nontrivial V := Module.finrank_pos_iff.mp hd
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
    · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
    · by_cases hW : W.toSubmodule = ⊥
      · exact Or.inl (Subrepresentation.ext hW)
      · refine Or.inr (Subrepresentation.ext ?_)
        set S := W.toSubmodule with hS
        have hSinv : ∀ v ∈ S, T v ∈ S := fun v hv =>
          W.apply_mem_toSubmodule ⟨A, Subgroup.mem_zpowers A⟩ hv
        have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hW
        have hTSint : IsIntegral k (T.restrict hSinv) := Algebra.IsIntegral.isIntegral _
        have hTSμ : aeval (T.restrict hSinv) μ = 0 := LinearMap.ext fun v => Subtype.ext (by
          rw [aeval_restrict_apply, minpoly.aeval]
          rfl)
        obtain ⟨r, hr⟩ := minpoly.dvd k _ hTSμ
        have hpos := minpoly.natDegree_pos hTSint
        rcases hμirr.isUnit_or_isUnit hr with hu | hu
        · rw [natDegree_eq_zero_of_isUnit hu] at hpos
          exact absurd hpos (lt_irrefl 0)
        · have hdegS : μ.natDegree = (minpoly k (T.restrict hSinv)).natDegree := by
            rw [hr, natDegree_mul (minpoly.ne_zero hTSint) hu.ne_zero,
              natDegree_eq_zero_of_isUnit hu, add_zero]
          have hle : (minpoly k (T.restrict hSinv)).natDegree ≤ Module.finrank k S := by
            rw [← LinearMap.charpoly_natDegree (T.restrict hSinv)]
            exact natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly _)
              (LinearMap.charpoly_monic _).ne_zero
          apply Submodule.eq_top_of_finrank_eq
          have := Submodule.finrank_le S
          omega

end CFSG.Semidihedral.Principal
