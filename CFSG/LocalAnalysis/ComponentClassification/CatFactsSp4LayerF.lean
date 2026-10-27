module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherFormZero

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K] {a : K}

theorem norm_qAlg (w : QuadraticAlgebra K a 0) :
    QuadraticAlgebra.norm w = w.re * w.re - a * w.im * w.im := by
  rw [QuadraticAlgebra.norm_def]
  ring

theorem eq_one_or_neg_of_sq_norm (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) {w : QuadraticAlgebra K a 0}
    (hw : w * w = 1) (hn : QuadraticAlgebra.norm w = 1) : w = 1 ∨ w = -1 := by
  have hre := congrArg QuadraticAlgebra.re hw
  have him := congrArg QuadraticAlgebra.im hw
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero] at hre him
  rw [norm_qAlg] at hn
  have hy : w.im = 0 := by
    have h1 : (2 * a) * (w.im * w.im) = 0 := by
      have : (1 : QuadraticAlgebra K a 0).re = 1 := rfl
      rw [this] at hre
      linear_combination hre - hn
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (mul_ne_zero h2 ha))
  have hx : w.re * w.re = 1 := by rw [hy] at hn; linear_combination hn
  rcases mul_self_eq_one_iff.mp hx with h | h
  · left
    exact QuadraticAlgebra.ext (by rw [h, QuadraticAlgebra.re_one])
      (by rw [hy, QuadraticAlgebra.im_one])
  · right
    exact QuadraticAlgebra.ext (by rw [h, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one])
      (by rw [hy, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one, neg_zero])

theorem not_sq_eq_neg_one (h2 : (2 : K) ≠ 0) (hna : ∀ l : K, l ^ 2 ≠ -a)
    {w : QuadraticAlgebra K a 0} (hw : w * w = -1) (hn : QuadraticAlgebra.norm w = 1) : False := by
  have hre := congrArg QuadraticAlgebra.re hw
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_neg] at hre
  rw [norm_qAlg] at hn
  have hre' : w.re * w.re + a * w.im * w.im = -1 := by
    have : (1 : QuadraticAlgebra K a 0).re = 1 := rfl
    rw [this] at hre
    exact hre
  have hx : w.re * w.re = 0 := by
    have : (2 : K) * (w.re * w.re) = 0 := by linear_combination hre' + hn
    exact (mul_eq_zero.mp this).resolve_left h2
  have hy : (-a) * (w.im * w.im) = 1 := by linear_combination hn - hx
  have him0 : w.im ≠ 0 := by
    rintro h0
    rw [h0, mul_zero, mul_zero] at hy
    exact zero_ne_one hy
  apply hna (w.im)⁻¹
  have : -a = (w.im * w.im)⁻¹ := eq_inv_of_mul_eq_one_left hy
  rw [this, inv_pow, sq]

theorem eq_one_or_neg_of_pow_two_pow (h2 : (2 : K) ≠ 0) (ha : a ≠ 0)
    (hna : ∀ l : K, l ^ 2 ≠ -a) :
    ∀ (k : ℕ) {w : QuadraticAlgebra K a 0}, QuadraticAlgebra.norm w = 1 → w ^ 2 ^ k = 1 →
      w = 1 ∨ w = -1 := by
  intro k
  induction k with
  | zero =>
    intro w _ hw
    left
    simpa using hw
  | succ k ih =>
    intro w hn hw
    have hn2 : QuadraticAlgebra.norm (w * w) = 1 := by rw [map_mul, hn, one_mul]
    have hw2 : (w * w) ^ 2 ^ k = 1 := by
      rw [← pow_two, ← pow_mul, ← pow_succ']
      exact hw
    rcases ih hn2 hw2 with h | h
    · exact eq_one_or_neg_of_sq_norm h2 ha h hn
    · exact (not_sq_eq_neg_one h2 hna h hn).elim

theorem exists_t [Finite K] (h5 : 5 ≤ Nat.card K) :
    ∃ t : K, t ≠ 0 ∧ 1 - a * t ^ 2 ≠ 0 := by
  by_contra h
  push Not at h
  have ha1 : a = 1 := by
    have := h 1 one_ne_zero
    rw [one_pow, mul_one] at this
    linear_combination -this
  have hall : ∀ t : K, t = 0 ∨ t = 1 ∨ t = -1 := by
    intro t
    by_cases ht : t = 0
    · exact Or.inl ht
    · right
      have := h t ht
      rw [ha1, one_mul] at this
      have h' : t * t = 1 := by rw [← pow_two]; linear_combination -this
      exact mul_self_eq_one_iff.mp h'
  classical
  have : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := by
    intro t _
    rcases hall t with h | h | h <;> simp [h]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
  have : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
  omega

theorem exists_odd_order_torus [Finite K] (h2 : (2 : K) ≠ 0) (h5 : 5 ≤ Nat.card K)
    (ha : a ≠ 0) (hna : ∀ l : K, l ^ 2 ≠ -a) :
    ∃ v : (QuadraticAlgebra K a 0)ˣ, QuadraticAlgebra.norm (v : QuadraticAlgebra K a 0) = 1 ∧
      Odd (orderOf v) ∧ orderOf v ≠ 1 := by
  have : Finite (QuadraticAlgebra K a 0) := Finite.of_equiv _ (QuadraticAlgebra.equivProd a 0).symm
  obtain ⟨t, ht0, ht1⟩ := exists_t (a := a) h5
  set c : K := (1 - a * t ^ 2)⁻¹ with hc
  set w : QuadraticAlgebra K a 0 := ⟨(1 + a * t ^ 2) * c, 2 * t * c⟩ with hw
  have hn : QuadraticAlgebra.norm w = 1 := by
    rw [norm_qAlg, hw, hc]
    field_simp
    ring
  have hu : IsUnit w := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [hn]; exact isUnit_one)
  set u := hu.unit with hudef
  have hne : (u : QuadraticAlgebra K a 0) ≠ 1 ∧ (u : QuadraticAlgebra K a 0) ≠ -1 := by
    have him : w.im ≠ 0 := by
      rw [hw]
      exact mul_ne_zero (mul_ne_zero h2 ht0) (inv_ne_zero ht1)
    refine ⟨fun h => him ?_, fun h => him ?_⟩
    · have := congrArg QuadraticAlgebra.im h
      rw [IsUnit.unit_spec] at this
      exact this
    · have := congrArg QuadraticAlgebra.im h
      rw [IsUnit.unit_spec, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one, neg_zero] at this
      exact this
  have ho : orderOf u ≠ 0 := (orderOf_pos u).ne'
  obtain ⟨j, m, hm, hjm⟩ := Nat.exists_eq_two_pow_mul_odd ho
  refine ⟨u ^ 2 ^ j, ?_, ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val, map_pow, IsUnit.unit_spec, hn, one_pow]
  · rw [orderOf_pow' u (pow_ne_zero _ two_ne_zero), hjm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
    exact hm
  · intro h1
    rw [orderOf_pow' u (pow_ne_zero _ two_ne_zero), hjm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (pow_pos two_pos j)] at h1
    have hpow : u ^ 2 ^ j = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hjm, h1, mul_one]
    have hpow' : (u : QuadraticAlgebra K a 0) ^ 2 ^ j = 1 := by
      rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
    rcases eq_one_or_neg_of_pow_two_pow h2 ha hna j (by rw [IsUnit.unit_spec]; exact hn) hpow'
      with h | h
    · exact hne.1 h
    · exact hne.2 h

end CFSG.ComponentClassification.CatFactsSp4
