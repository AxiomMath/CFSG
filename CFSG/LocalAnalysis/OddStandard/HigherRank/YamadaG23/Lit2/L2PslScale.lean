module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem l2_scale_involution {K : Type} [Field K] [Finite K] (hq : Nat.card K % 4 = 1) {n : ℕ}
    (hn : 0 < n) (x x' k m : Matrix.SpecialLinearGroup (Fin n) K)
    (hc : x * x'⁻¹ ∈ center (Matrix.SpecialLinearGroup (Fin n) K))
    (hk : k ∈ center (Matrix.SpecialLinearGroup (Fin n) K)) (hko : Odd (orderOf k))
    (hm : (m : Matrix (Fin n) (Fin n) K) = -1) (h2 : x' * x' = k ∨ x' * x' = m * k) :
    ∃ μ : K, μ ≠ 0 ∧
      (μ • (x : Matrix (Fin n) (Fin n) K)) * (μ • (x : Matrix (Fin n) (Fin n) K)) = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K % 4 = 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hq
  have hne : Fintype.card K % 4 ≠ 3 := by rw [hcard]; decide
  obtain ⟨b, hb⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).mpr hne
  obtain ⟨s, hs, hsc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  obtain ⟨r, hr, hrk⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
  have hs' : s ^ n = 1 := by simpa using hs
  have hr' : r ^ n = 1 := by simpa using hr
  have hs0 : s ≠ 0 := by
    intro h; rw [h, zero_pow hn.ne'] at hs'; exact zero_ne_one hs'
  have hr0 : r ≠ 0 := by
    intro h; rw [h, zero_pow hn.ne'] at hr'; exact zero_ne_one hr'
  have hkpow : (k : Matrix (Fin n) (Fin n) K) ^ orderOf k = 1 := by
    have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin n) K =>
      (z : Matrix (Fin n) (Fin n) K)) (pow_orderOf_eq_one k)
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using h
  have hro : r ^ orderOf k = 1 := by
    have hmat : Matrix.scalar (Fin n) (r ^ orderOf k) = (1 : Matrix (Fin n) (Fin n) K) := by
      rw [map_pow, hrk, hkpow]
    have hi := congrFun (congrFun hmat ⟨0, hn⟩) ⟨0, hn⟩
    simpa [Matrix.scalar_apply] using hi
  obtain ⟨t, ht⟩ := hko
  have hro' : r ^ (2 * t + 1) = 1 := by simpa [ht] using hro
  have h1 : r ^ (2 * (t + 1)) = r := by
    have : 2 * (t + 1) = 2 * t + 1 + 1 := by ring
    rw [this, pow_succ, hro', one_mul]
  have hsq : (r ^ (t + 1)) * (r ^ (t + 1)) = r ^ (2 * (t + 1)) := by
    rw [← pow_two, ← pow_mul, show (t + 1) * 2 = 2 * (t + 1) by ring]
  let a := r ^ (t + 1)
  have ha : r = a * a := h1.symm.trans hsq.symm
  have ha0 : a ≠ 0 := pow_ne_zero (t + 1) hr0
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, mul_zero] at hb
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)) hb
  have hscalar : ∀ c : K, Matrix.scalar (Fin n) c = c • (1 : Matrix (Fin n) (Fin n) K) := by
    intro c
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have hx : x = (x * x'⁻¹) * x' := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have hcx : ((x * x'⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = Matrix.scalar (Fin n) s := hsc.symm
  have hX : (x : Matrix (Fin n) (Fin n) K) = s • (x' : Matrix (Fin n) (Fin n) K) := by
    calc (x : Matrix (Fin n) (Fin n) K)
        = (((x * x'⁻¹) * x' : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) :=
          congrArg (fun z : Matrix.SpecialLinearGroup (Fin n) K =>
            (z : Matrix (Fin n) (Fin n) K)) hx
      _ = ((x * x'⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
            * (x' : Matrix (Fin n) (Fin n) K) := by
          rw [Matrix.SpecialLinearGroup.coe_mul]
      _ = Matrix.scalar (Fin n) s * (x' : Matrix (Fin n) (Fin n) K) := by rw [hcx]
      _ = (s • (1 : Matrix (Fin n) (Fin n) K)) * (x' : Matrix (Fin n) (Fin n) K) := by
          rw [hscalar s]
      _ = s • (x' : Matrix (Fin n) (Fin n) K) := by rw [Matrix.smul_mul, one_mul]
  have hXX0 : (x : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)
      = (s * s) •
        ((x' * x' : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hX, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.SpecialLinearGroup.coe_mul]
  have key : ∀ (lam nu : K), nu ≠ 0 → lam = nu * nu →
      (x : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) = lam • 1 →
      (nu⁻¹ • (x : Matrix (Fin n) (Fin n) K)) *
        (nu⁻¹ • (x : Matrix (Fin n) (Fin n) K)) = 1 := by
    intro lam nu hnu hlam hXX
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hXX, hlam, smul_smul]
    have h1 : (nu⁻¹ * nu⁻¹) * (nu * nu) = 1 := by
      rw [← mul_inv, inv_mul_cancel₀ (mul_ne_zero hnu hnu)]
    rw [h1, one_smul]
  rcases h2 with h2a | h2b
  · have hXXA : (x : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)
        = (s * s * r) • 1 := by
      rw [hXX0, h2a, ← hrk, hscalar r, smul_smul]
    have hlam : s * s * r = (s * a) * (s * a) := by rw [ha]; ring
    exact ⟨(s * a)⁻¹, inv_ne_zero (mul_ne_zero hs0 ha0),
      key (s * s * r) (s * a) (mul_ne_zero hs0 ha0) hlam hXXA⟩
  · have hXXB : (x : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)
        = (-(s * s * r)) • 1 := by
      rw [hXX0, h2b, Matrix.SpecialLinearGroup.coe_mul, hm, ← hrk, hscalar r, neg_one_mul,
        ← neg_smul, smul_smul, show (s * s) * -r = -(s * s * r) by ring]
    have hlam : -(s * s * r) = (s * a * b) * (s * a * b) := by
      rw [show (s * a * b) * (s * a * b) = (s * a) * (s * a) * (b * b) by ring,
        show (s * a) * (s * a) = s * s * r by rw [ha]; ring, ← hb]
      ring
    exact ⟨(s * a * b)⁻¹, inv_ne_zero (mul_ne_zero (mul_ne_zero hs0 ha0) hb0),
      key (-(s * s * r)) (s * a * b) (mul_ne_zero (mul_ne_zero hs0 ha0) hb0) hlam hXXB⟩

end CFSG.OddStandard.HigherRank.YamadaG23
