module

public import CFSG.FeitThompson.Representations.IntegralRemainderOneCharacterExtension
import CFSG.FeitThompson.Representations.ExtensionCoefficientsFollowDegrees
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FeitExtension

namespace OneCharExtension

open scoped ComplexOrder

variable {G : Type*} [Group G] [Fintype G] {L : Type*} [Group L] [Fintype L]
  {ι : Type*} [Fintype ι] {γ : ι → (L → ℂ)} {χ : L → ℂ} {d : ℤ} {k₀ : ι}
  (E : OneCharExtension G γ χ d k₀) [DecidableEq ι]

theorem bCoeff_eq_zero_of_lt_degreeSqSum
    (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ) (j : ι) : E.bCoeff j = 0 := by
  choose n hn0 hn using E.exists_degree
  choose b hb using E.exists_int_bCoeff
  obtain ⟨N, hN⟩ := E.exists_int_cfInner_self_remainder
  obtain ⟨k, hk0, hk⟩ := E.exists_degree_ratio
  have hid : N + ∑ i, b i ^ 2 = 1 + 2 * d * b k₀ := E.int_remainder_add_sum_sq hb hN
  have hN0 : 0 ≤ N := by
    have h := cfInner_self_nonneg E.remainder
    rw [hN] at h
    have hcast : ((N : ℝ) : ℂ) = (N : ℂ) := by push_cast; ring
    rw [← hcast, Complex.zero_le_real] at h
    exact_mod_cast h
  have hprop : ∀ i, (n k₀ : ℤ) * b i = (n i : ℤ) * b k₀ := by
    intro i
    have h := E.apply_one_mul_bCoeff i
    rw [hn, hn, hb, hb] at h
    exact_mod_cast h
  have hnk : (0 : ℤ) < (n k₀ : ℤ) := by exact_mod_cast hn0 k₀
  have hnsq : (0 : ℤ) < (n k₀ : ℤ) ^ 2 := by positivity
  have hWint : 2 * d * (n k₀ : ℤ) ^ 2 < ∑ i, (n i : ℤ) ^ 2 := by
    rw [E.chi_apply_one, degreeSqSum_eq] at hW
    simp only [hn] at hW
    have h2 : ((2 * d * (n k₀ : ℤ) ^ 2 : ℤ) : ℂ) = 2 * (n k₀ : ℂ) * ((d : ℂ) * (n k₀ : ℂ)) := by
      push_cast; ring
    have h3 : ((∑ i, (n i : ℤ) ^ 2 : ℤ) : ℂ) = ∑ i, ((n i : ℂ)) ^ 2 := by push_cast; ring
    have key : ((2 * d * (n k₀ : ℤ) ^ 2 : ℤ) : ℂ) < ((∑ i, (n i : ℤ) ^ 2 : ℤ) : ℂ) := by
      rw [h2, h3]; exact hW
    exact_mod_cast key
  have hzero : b k₀ = 0 := by
    by_contra hbk
    have hbsq : (0 : ℤ) < b k₀ ^ 2 := by positivity
    have hkey : (n k₀ : ℤ) ^ 2 * ∑ i, b i ^ 2 = b k₀ ^ 2 * ∑ i, (n i : ℤ) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      linear_combination ((n k₀ : ℤ) * b i + (n i : ℤ) * b k₀) * hprop i
    have h1 : b k₀ ^ 2 * (2 * d * (n k₀ : ℤ) ^ 2) < b k₀ ^ 2 * ∑ i, (n i : ℤ) ^ 2 :=
      mul_lt_mul_of_pos_left hWint hbsq
    have hsum : 2 * d * b k₀ ^ 2 < ∑ i, b i ^ 2 := by
      have h2 : (n k₀ : ℤ) ^ 2 * (2 * d * b k₀ ^ 2) < (n k₀ : ℤ) ^ 2 * ∑ i, b i ^ 2 := by
        rw [hkey]; linarith
      exact lt_of_mul_lt_mul_left h2 hnsq.le
    have hbb : 0 ≤ b k₀ * (b k₀ - 1) := by
      rcases lt_trichotomy (b k₀) 0 with h | h | h
      · nlinarith
      · exact absurd h hbk
      · have h1 : 1 ≤ b k₀ := by omega
        nlinarith
    have hd1 : 1 ≤ d := E.d_pos
    have hlt : N + 2 * d * (b k₀ * (b k₀ - 1)) < 1 := by nlinarith [hid, hsum]
    have hXnn : 0 ≤ 2 * d * (b k₀ * (b k₀ - 1)) := mul_nonneg (by linarith) hbb
    have hNz : N = 0 := le_antisymm (by linarith) hN0
    have hX : b k₀ * (b k₀ - 1) = 0 := by
      have h0 : 2 * d * (b k₀ * (b k₀ - 1)) = 0 := le_antisymm (by linarith) hXnn
      rcases mul_eq_zero.mp h0 with h | h
      · omega
      · exact h
    have hb1 : b k₀ = 1 := by
      rcases mul_eq_zero.mp hX with h | h
      · exact absurd h hbk
      · omega
    have hΔ : E.remainder = 0 := by
      refine cfInner_self_eq_zero.mp ?_
      rw [hN, hNz]; simp
    have hsum1 : (0 : ℂ)
        = (d : ℂ) * ((k : ℂ) * γ k₀ 1) - ∑ i, E.bCoeff i * ((k : ℂ) * γ i 1) := by
      have h := congrFun hΔ 1
      rw [remainder_apply] at h
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
        E.alpha_apply_one, hk, zero_add, Pi.zero_apply] at h
      linear_combination -h
    have hkne : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk0
    have hsumeq : ∑ i, E.bCoeff i * ((k : ℂ) * γ i 1)
        = (k : ℂ) * ∑ i, (b i : ℂ) * (n i : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hb, hn]; ring
    have hdeg : ∑ i, b i * (n i : ℤ) = d * (n k₀ : ℤ) := by
      have hfactor : (k : ℂ) * ((d : ℂ) * (n k₀ : ℂ) - ∑ i, (b i : ℂ) * (n i : ℂ)) = 0 := by
        rw [mul_sub, ← hsumeq, ← hn k₀]
        linear_combination -hsum1
      have h := (mul_eq_zero.mp hfactor).resolve_left hkne
      have hcast : ((∑ i, b i * (n i : ℤ) : ℤ) : ℂ) = ((d * (n k₀ : ℤ) : ℤ) : ℂ) := by
        push_cast
        linear_combination -h
      exact_mod_cast hcast
    have hWeq : ∑ i, (n i : ℤ) ^ 2 = d * (n k₀ : ℤ) ^ 2 := by
      have h1 : (n k₀ : ℤ) * ∑ i, b i * (n i : ℤ) = ∑ i, (n i : ℤ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h := hprop i
        rw [hb1] at h
        linear_combination (n i : ℤ) * h
      rw [hdeg] at h1
      linarith [h1]
    nlinarith [hWint, hWeq, mul_pos (show (0 : ℤ) < d from E.d_pos) hnsq]
  have hbj : b j = 0 := by
    have h : (n k₀ : ℤ) * b j = 0 := by rw [hprop j, hzero, mul_zero]
    exact (mul_eq_zero.mp h).resolve_left (by omega)
  rw [hb, hbj]
  simp

theorem cfInner_self_remainder_of_lt_degreeSqSum
    (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ) :
    cfInner E.remainder E.remainder = 1 := by
  have h := E.cfInner_self_remainder_add_sum_sq
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [E.bCoeff_eq_zero_of_lt_degreeSqSum hW i],
    E.bCoeff_eq_zero_of_lt_degreeSqSum hW k₀] at h
  simpa using h

theorem remainder_eq_of_lt_degreeSqSum (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ) :
    E.remainder = E.alpha + (d : ℂ) • E.nuImage k₀ := by
  rw [remainder_apply, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [E.bCoeff_eq_zero_of_lt_degreeSqSum hW i, zero_smul]]
  simp

theorem cfInner_alpha_nuImage_of_lt_degreeSqSum (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ) (j : ι) :
    cfInner E.alpha (E.nuImage j) = -((d : ℂ) * (if j = k₀ then 1 else 0)) := by
  have h := E.bCoeff_eq_zero_of_lt_degreeSqSum hW j
  rw [bCoeff_apply] at h
  linear_combination h

end OneCharExtension

end FeitExtension

end CFSG.FeitThompson
