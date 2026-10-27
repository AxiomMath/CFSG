module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

public section

open scoped BigOperators ComplexConjugate

namespace CFSG.Wreathed.ConditionalFourier

@[expose] noncomputable def fourierTransform (m : ℕ) (ζ : ℂ) (v : ℕ → ℂ) (j : ℕ) : ℂ :=
  (m : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) * v k

theorem sum_range_pow_eq_zero {x : ℂ} {m : ℕ} (hx : x ^ m = 1) (hx1 : x ≠ 1) :
    ∑ k ∈ Finset.range m, x ^ k = 0 := by
  have h := geom_sum_mul x m
  rw [hx, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hx1)

theorem sum_range_pow_mul {ζ : ℂ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (c : ℕ) :
    ∑ k ∈ Finset.range m, ζ ^ (c * k) = if m ∣ c then (m : ℂ) else 0 := by
  split_ifs with hc
  · have h1 : ∀ k, ζ ^ (c * k) = 1 := by
      intro k
      obtain ⟨d, rfl⟩ := hc
      rw [mul_assoc, pow_mul, hζ.pow_eq_one, one_pow]
    simp [h1]
  · have hx : (ζ ^ c) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hx1 : ζ ^ c ≠ 1 := fun h => hc (hζ.dvd_of_pow_eq_one c h)
    have h := sum_range_pow_eq_zero hx hx1
    simpa [← pow_mul] using h

theorem sum_Ico_pow_mul {ζ : ℂ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm : 1 ≤ m) (c : ℕ) :
    ∑ k ∈ Finset.Ico 1 m, ζ ^ (c * k) = (if m ∣ c then (m : ℂ) else 0) - 1 := by
  have h := sum_range_pow_mul hζ c
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hm,
    Finset.sum_Ico_succ_top (Nat.zero_le 0), Finset.Ico_self, Finset.sum_empty] at h
  simp only [mul_zero, pow_zero, zero_add] at h
  linear_combination h

theorem conj_pow_eq {ζ : ℂ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm : 1 ≤ m) {j : ℕ}
    (hj : j ≤ m) (k : ℕ) : conj (ζ ^ (j * k)) = ζ ^ ((m - j) * k) := by
  have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hconj : conj ζ = ζ⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
    simp
  rw [map_pow, hconj, inv_pow]
  have hprod : ζ ^ (j * k) * ζ ^ ((m - j) * k) = 1 := by
    rw [← pow_add, ← add_mul, Nat.add_sub_cancel' hj, pow_mul, hζ.pow_eq_one, one_pow]
  rw [inv_eq_of_mul_eq_one_right hprod]

theorem sum_conj_sub_one_mul_sub_one {ζ : ℂ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) {j t : ℕ}
    (hj1 : 1 ≤ j) (hjm : j < m) (ht1 : 1 ≤ t) (htm : t < m) :
    ∑ k ∈ Finset.Ico 1 m, conj (ζ ^ (j * k) - 1) * (ζ ^ (t * k) - 1) =
      (m : ℂ) * ((if j = t then 1 else 0) + 1) := by
  have hm : 1 ≤ m := by omega
  have hterm : ∀ k ∈ Finset.Ico 1 m, conj (ζ ^ (j * k) - 1) * (ζ ^ (t * k) - 1) =
      ζ ^ ((m - j + t) * k) - ζ ^ ((m - j) * k) - ζ ^ (t * k) + 1 := by
    intro k _
    rw [map_sub, map_one, conj_pow_eq hζ hm hjm.le, add_mul, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, sum_Ico_pow_mul hζ hm, sum_Ico_pow_mul hζ hm,
    sum_Ico_pow_mul hζ hm, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have h1 : ¬ m ∣ (m - j) := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have h2 : ¬ m ∣ t := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have h3 : m ∣ (m - j + t) ↔ j = t := by
    constructor
    · intro h
      obtain ⟨c, hc⟩ := h
      rcases c with _ | _ | c
      · omega
      · omega
      · have h2m : m * 2 ≤ m * (c + 1 + 1) := Nat.mul_le_mul_left m (by omega)
        omega
    · rintro rfl
      exact ⟨1, by omega⟩
  rw [ite_eq_right h1, ite_eq_right h2]
  push_cast [Nat.cast_sub hm]
  by_cases hjt : j = t
  · rw [ite_eq_left (h3.mpr hjt), ite_eq_left hjt]
    ring
  · rw [ite_eq_right (fun h => hjt (h3.mp h)), ite_eq_right hjt]
    ring

theorem fourierTransform_one {ζ : ℂ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) {j : ℕ} (hj1 : 1 ≤ j)
    (hjm : j < m) : fourierTransform m ζ (fun _ => 1) j = -1 := by
  have hm : 1 ≤ m := by omega
  have hdvd : ¬ m ∣ j := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  unfold fourierTransform
  simp only [mul_one]
  rw [Finset.sum_sub_distrib, sum_Ico_pow_mul hζ hm, ite_eq_right hdvd, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul, mul_one]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  push_cast [Nat.cast_sub hm]
  field_simp
  ring

theorem fourierTransform_zero (m : ℕ) (ζ : ℂ) (j : ℕ) :
    fourierTransform m ζ (fun _ => 0) j = 0 := by
  simp [fourierTransform]

theorem fourierTransform_inversion {ζ : ℂ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (v : ℕ → ℂ)
    {k : ℕ} (hk1 : 1 ≤ k) (hkm : k < m) :
    ∑ j ∈ Finset.Ico 1 m, ζ ^ ((m - k) * j) * fourierTransform m ζ v j = v k := by
  have hm : 1 ≤ m := by omega
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold fourierTransform
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ h ∈ Finset.Ico 1 m, ∑ j ∈ Finset.Ico 1 m,
      ζ ^ ((m - k) * j) * ((m : ℂ)⁻¹ * ((ζ ^ (j * h) - 1) * v h)) =
        (m : ℂ)⁻¹ * v h * (∑ j ∈ Finset.Ico 1 m, ζ ^ ((m - k + h) * j) -
          ∑ j ∈ Finset.Ico 1 m, ζ ^ ((m - k) * j)) := by
    intro h _
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_mul, pow_add, mul_comm j h]
    ring
  rw [Finset.sum_congr rfl hinner]
  have hkdvd : ¬ m ∣ (m - k) := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hdvd : ∀ h ∈ Finset.Ico 1 m, (m ∣ (m - k + h) ↔ h = k) := by
    intro h hh
    rw [Finset.mem_Ico] at hh
    constructor
    · intro hd
      obtain ⟨c, hc⟩ := hd
      rcases c with _ | _ | c
      · omega
      · omega
      · have h2m : m * 2 ≤ m * (c + 1 + 1) := Nat.mul_le_mul_left m (by omega)
        omega
    · rintro rfl
      exact ⟨1, by omega⟩
  have hval : ∀ h ∈ Finset.Ico 1 m, (m : ℂ)⁻¹ * v h * (∑ j ∈ Finset.Ico 1 m,
      ζ ^ ((m - k + h) * j) - ∑ j ∈ Finset.Ico 1 m, ζ ^ ((m - k) * j)) =
        if h = k then v h else 0 := by
    intro h hh
    rw [sum_Ico_pow_mul hζ hm, sum_Ico_pow_mul hζ hm, ite_eq_right hkdvd]
    by_cases hhk : h = k
    · rw [ite_eq_left ((hdvd h hh).mpr hhk), ite_eq_left hhk]
      field_simp
      ring
    · rw [ite_eq_right (fun hd => hhk ((hdvd h hh).mp hd)), ite_eq_right hhk]
      ring
  rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq']
  rw [ite_eq_left (Finset.mem_Ico.mpr ⟨hk1, hkm⟩)]

theorem fourierTransform_gram {ι : Type*} (B : Finset ι) {ζ : ℂ} {m : ℕ}
    (hζ : IsPrimitiveRoot ζ m) (v w : ι → ℕ → ℂ) (c : ℂ)
    (hvw : ∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m,
      ∑ χ ∈ B, conj (v χ k) * w χ h = if k = h then c else 0)
    {j t : ℕ} (hj1 : 1 ≤ j) (hjm : j < m) (ht1 : 1 ≤ t) (htm : t < m) :
    ∑ χ ∈ B, conj (fourierTransform m ζ (v χ) j) * fourierTransform m ζ (w χ) t =
      ((if j = t then 1 else 0) + 1) * c / m := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold fourierTransform
  have hexpand : ∀ χ ∈ B, conj ((m : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) * v χ k) *
      ((m : ℂ)⁻¹ * ∑ h ∈ Finset.Ico 1 m, (ζ ^ (t * h) - 1) * w χ h) =
        ((m : ℂ)⁻¹ * (m : ℂ)⁻¹) * ∑ k ∈ Finset.Ico 1 m, ∑ h ∈ Finset.Ico 1 m,
          (conj (ζ ^ (j * k) - 1) * (ζ ^ (t * h) - 1)) * (conj (v χ k) * w χ h) := by
    intro χ _
    rw [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
    rw [show ((m : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 m, conj ((ζ ^ (j * k) - 1) * v χ k)) *
        ((m : ℂ)⁻¹ * ∑ h ∈ Finset.Ico 1 m, (ζ ^ (t * h) - 1) * w χ h) =
        ((m : ℂ)⁻¹ * (m : ℂ)⁻¹) * ((∑ k ∈ Finset.Ico 1 m, conj ((ζ ^ (j * k) - 1) * v χ k)) *
          ∑ h ∈ Finset.Ico 1 m, (ζ ^ (t * h) - 1) * w χ h) by ring]
    rw [Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun h _ => ?_
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl hexpand, ← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ k ∈ Finset.Ico 1 m, ∑ χ ∈ B, ∑ h ∈ Finset.Ico 1 m,
      (conj (ζ ^ (j * k) - 1) * (ζ ^ (t * h) - 1)) * (conj (v χ k) * w χ h) =
        conj (ζ ^ (j * k) - 1) * (ζ ^ (t * k) - 1) * c := by
    intro k hk
    rw [Finset.sum_comm]
    have h' : ∀ h ∈ Finset.Ico 1 m, ∑ χ ∈ B,
        (conj (ζ ^ (j * k) - 1) * (ζ ^ (t * h) - 1)) * (conj (v χ k) * w χ h) =
          if k = h then conj (ζ ^ (j * k) - 1) * (ζ ^ (t * h) - 1) * c else 0 := by
      intro h hh
      rw [← Finset.mul_sum, hvw k hk h hh]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl h', Finset.sum_ite_eq, ite_eq_left hk]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul,
    sum_conj_sub_one_mul_sub_one hζ hj1 hjm ht1 htm]
  field_simp

theorem fourierTransform_congr {m : ℕ} {ζ : ℂ} {v w : ℕ → ℂ}
    (h : ∀ k ∈ Finset.Ico 1 m, v k = w k) (j : ℕ) :
    fourierTransform m ζ v j = fourierTransform m ζ w j := by
  unfold fourierTransform
  rw [Finset.sum_congr rfl fun k hk => by rw [h k hk]]

theorem zpow_neg_mul_eq_pow {ζ : ℂ} {m : ℕ} (hm : 1 ≤ m) (hζ : ζ ^ m = 1) {j k : ℕ}
    (hk : k ≤ m) : ζ ^ (-((j : ℤ) * k)) = ζ ^ ((m - k) * j) := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hζ
    exact zero_ne_one hζ
  have hζ' : ζ ^ (m : ℤ) = 1 := by rw [zpow_natCast, hζ]
  rw [← zpow_natCast, show (((m - k) * j : ℕ) : ℤ) = (m : ℤ) * j - (j : ℤ) * k by
    push_cast [Nat.cast_sub hk]; ring, zpow_sub₀ hζ0, zpow_mul, hζ', one_zpow, one_div,
    ← zpow_neg]

end CFSG.Wreathed.ConditionalFourier
