module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def eigenProj (B : Matrix ι ι K) (t : K) : Matrix ι ι K :=
  1 + t ^ 2 • B + t • B ^ 2

theorem exists_cube_root {n : ℕ} (h : UnitaryFieldData 2 n K) (hn : Even n) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 ∧ h.bar ω = ω := by
  haveI : Finite K := h.finite
  have hcard_units : Nat.card Kˣ = 2 ^ (2 * n) - 1 := by
    rw [Nat.card_units, h.card]
  rcases even_iff_exists_two_mul.mp hn with ⟨m, rfl⟩
  have h3dvd : 3 ∣ Nat.card Kˣ := by
    rw [hcard_units, show 2 * (2 * m) = 4 * m by ring, pow_mul,
      show (2 : ℕ) ^ 4 = 16 by norm_num]
    have h16 : (16 : ℕ) ≡ 1 [MOD 3] := by decide
    have hp : (16 : ℕ) ^ m ≡ 1 [MOD 3] := by simpa using h16.pow m
    exact hp.symm.dvd'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3dvd
  have hx3 : x ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hx)
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    norm_num at hx
  have hω3 : (x : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  have hω_ne : (x : K) ≠ 1 := fun h1 => hx1 (Units.ext h1)
  have hωquad : (x : K) ^ 2 + (x : K) + 1 = 0 := by
    have hfac : ((x : K) - 1) * ((x : K) ^ 2 + (x : K) + 1) = 0 := by
      rw [show ((x : K) - 1) * ((x : K) ^ 2 + (x : K) + 1) = (x : K) ^ 3 - 1 by ring,
        hω3, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hω_ne)
  refine ⟨(x : K), hωquad, ?_⟩
  rw [h.bar_apply, ← Units.val_pow_eq_pow_val]
  refine congrArg Units.val ?_
  have h3dvd2 : 3 ∣ 2 ^ (2 * m) - 1 := by
    rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
    have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    have hp : (4 : ℕ) ^ m ≡ 1 [MOD 3] := by simpa using h4.pow m
    exact hp.symm.dvd'
  have hpow1 : x ^ (2 ^ (2 * m) - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hx]; exact h3dvd2)
  calc x ^ (2 ^ (2 * m)) = x ^ (2 ^ (2 * m) - 1 + 1) := by
        rw [Nat.sub_add_cancel Nat.one_le_two_pow]
    _ = x ^ (2 ^ (2 * m) - 1) * x := by rw [pow_succ]
    _ = 1 * x := by rw [hpow1]
    _ = x := one_mul x

variable [CharP K 2] {B : Matrix ι ι K}

private theorem mul_poly (hB3 : B ^ 3 = 1) (c0 c1 c2 d0 d1 d2 : K) :
    (c0 • 1 + c1 • B + c2 • B ^ 2) * (d0 • 1 + d1 • B + d2 • B ^ 2) =
      (c0 * d0 + c1 * d2 + c2 * d1) • 1 +
        (c0 * d1 + c1 * d0 + c2 * d2) • B +
          (c0 * d2 + c1 * d1 + c2 * d0) • B ^ 2 := by
  have hB4 : B ^ 4 = B := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hB3, one_mul]
  have hBB : B * B = B ^ 2 := by rw [sq]
  have hBB2 : B * B ^ 2 = 1 := by rw [← pow_succ']; exact hB3
  have hB2B : B ^ 2 * B = 1 := by rw [← pow_succ]; exact hB3
  have hB2B2 : B ^ 2 * B ^ 2 = B := by rw [← sq, ← pow_mul]; exact hB4
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    hBB, hBB2, hB2B, hB2B2, smul_smul]
  module

private theorem mul_poly_one (hB3 : B ^ 3 = 1) (a1 a2 b1 b2 : K) :
    (1 + a1 • B + a2 • B ^ 2) * (1 + b1 • B + b2 • B ^ 2) =
      (1 + a1 * b2 + a2 * b1) • 1 + (b1 + a1 + a2 * b2) • B +
        (b2 + a1 * b1 + a2) • B ^ 2 := by
  have h := mul_poly hB3 1 a1 a2 1 b1 b2
  simpa only [one_smul, one_mul, mul_one] using h

private theorem eq_of_coeff_one {a1 a2 b1 b2 : K} (h1 : a1 = b1) (h2 : a2 = b2) :
    (1 : Matrix ι ι K) + a1 • B + a2 • B ^ 2 = 1 + b1 • B + b2 • B ^ 2 := by
  rw [h1, h2]

private theorem eq_of_coeff {a0 a1 a2 b0 b1 b2 : K} (h0 : a0 = b0) (h1 : a1 = b1)
    (h2 : a2 = b2) :
    a0 • (1 : Matrix ι ι K) + a1 • B + a2 • B ^ 2 =
      b0 • (1 : Matrix ι ι K) + b1 • B + b2 • B ^ 2 := by
  rw [h0, h1, h2]

private theorem mul_poly_B (hB3 : B ^ 3 = 1) (d1 d2 : K) :
    B * (1 + d1 • B + d2 • B ^ 2) = d2 • 1 + (1 : K) • B + d1 • B ^ 2 := by
  have hBB : B * B = B ^ 2 := by rw [sq]
  have hBB2 : B * B ^ 2 = 1 := by rw [← pow_succ']; exact hB3
  simp only [mul_add, mul_one, Matrix.mul_smul, hBB, hBB2]
  module

theorem mul_eigenProj (hB3 : B ^ 3 = 1) {t : K} (ht : t ^ 3 = 1) :
    B * eigenProj B t = t • eigenProj B t := by
  simp only [eigenProj]
  rw [mul_poly_B hB3 (t ^ 2) t]
  simp only [smul_add, smul_smul]
  apply eq_of_coeff
  · rfl
  · rw [← pow_succ', ht]
  · rw [← sq]

theorem eigenProj_mul_self (hB3 : B ^ 3 = 1) {t : K} (ht : t ^ 3 = 1) :
    eigenProj B t * eigenProj B t = eigenProj B t := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ht4 : t ^ 4 = t := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, ht, one_mul]
  simp only [eigenProj]
  rw [mul_poly_one hB3 (t ^ 2) t (t ^ 2) t]
  rw [show (1 : K) + t ^ 2 * t + t * t ^ 2 = 1 by
    rw [show t ^ 2 * t = 1 by rw [← pow_succ]; exact ht,
      show t * t ^ 2 = 1 by rw [← pow_succ']; exact ht]
    linear_combination h2]
  simp only [one_smul]
  apply eq_of_coeff_one
  · rw [← sq]
    linear_combination (t ^ 2) * h2
  · rw [show t ^ 2 * t ^ 2 = t by rw [← sq, ← pow_mul]; exact ht4]
    linear_combination t * h2

theorem eigenProj_mul_eigenProj (hB3 : B ^ 3 = 1) {s t : K} (hs : s ^ 3 = 1) (ht : t ^ 3 = 1)
    (hst : s ≠ t) : eigenProj B s * eigenProj B t = 0 := by
  have hquad : s ^ 2 + s * t + t ^ 2 = 0 := by
    have h1 : (s - t) * (s ^ 2 + s * t + t ^ 2) = 0 := by
      calc (s - t) * (s ^ 2 + s * t + t ^ 2) = s ^ 3 - t ^ 3 := by ring
        _ = 0 := by rw [hs, ht, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (sub_ne_zero.mpr hst)
    · exact h
  simp only [eigenProj]
  rw [mul_poly_one hB3 (s ^ 2) s (t ^ 2) t]
  have hs' : s * (s ^ 2 + s * t + t ^ 2) = 0 := by rw [hquad, mul_zero]
  have hthis : s * (s ^ 2 + s * t + t ^ 2) = 1 + s ^ 2 * t + s * t ^ 2 := by
    calc s * (s ^ 2 + s * t + t ^ 2) = s ^ 3 + s ^ 2 * t + s * t ^ 2 := by ring
      _ = 1 + s ^ 2 * t + s * t ^ 2 := by rw [hs]
  have hc0 : (1 : K) + s ^ 2 * t + s * t ^ 2 = 0 := by
    rw [← hthis]; exact hs'
  have hc1 : t ^ 2 + s ^ 2 + s * t = 0 := by linear_combination hquad
  have hst' : s * t * (s ^ 2 + s * t + t ^ 2) = 0 := by rw [hquad, mul_zero]
  have hthis2 : s * t * (s ^ 2 + s * t + t ^ 2) = t + s ^ 2 * t ^ 2 + s := by
    calc s * t * (s ^ 2 + s * t + t ^ 2) = s ^ 3 * t + s ^ 2 * t ^ 2 + s * t ^ 3 := by ring
      _ = t + s ^ 2 * t ^ 2 + s := by rw [hs, ht]; ring
  have hc2 : t + s ^ 2 * t ^ 2 + s = 0 := by
    rw [← hthis2]; exact hst'
  rw [hc0, hc1, hc2]
  simp

theorem eigenProj_add (hB3 : B ^ 3 = 1) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    eigenProj B 1 + eigenProj B ω + eigenProj B (ω ^ 2) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω4 : (ω ^ 2) ^ 2 = ω := by linear_combination (ω ^ 2 - ω) * hω
  have hA : (1 : K) + ω ^ 2 + ω = 0 := by linear_combination hω
  have hB' : (1 : K) + ω + ω ^ 2 = 0 := by linear_combination hω
  have h3 : (3 : K) = 1 := by linear_combination h2
  simp only [eigenProj]
  rw [hω4]
  simp only [one_pow, one_smul]
  have hcoll : (1 + B + B ^ 2) + (1 + ω ^ 2 • B + ω • B ^ 2) +
      (1 + ω • B + ω ^ 2 • B ^ 2) =
      (3 : K) • 1 + ((1 : K) + ω ^ 2 + ω) • B + ((1 : K) + ω + ω ^ 2) • B ^ 2 := by
    module
  rw [hcoll, hA, hB', zero_smul, zero_smul, add_zero, add_zero, h3, one_smul]

theorem map_transpose_eigenProj (σ : K →+* K) (hB : (B.map σ)ᵀ * B = 1) (hB3 : B ^ 3 = 1) {t : K}
    (ht : t ^ 3 = 1) (hσ : σ t = t) : ((eigenProj B t).map σ)ᵀ = eigenProj B (t ^ 2) := by
  have ht4 : t ^ 4 = t := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, ht, one_mul]
  have hB4 : B ^ 4 = B := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hB3, one_mul]
  have hBB2 : B * B ^ 2 = 1 := by rw [← pow_succ']; exact hB3
  have hBinv : (B.map σ)ᵀ = B ^ 2 := by
    calc (B.map σ)ᵀ = (B.map σ)ᵀ * (B * B ^ 2) := by rw [hBB2, Matrix.mul_one]
      _ = ((B.map σ)ᵀ * B) * B ^ 2 := by rw [Matrix.mul_assoc]
      _ = B ^ 2 := by rw [hB, Matrix.one_mul]
  have hmap : (eigenProj B t).map σ = 1 + σ (t ^ 2) • B.map σ + σ t • (B.map σ) ^ 2 := by
    simp only [eigenProj, Matrix.map_add σ (map_add σ),
      Matrix.map_smul' σ (t ^ 2) B (map_mul σ), Matrix.map_smul' σ t (B ^ 2) (map_mul σ),
      Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.map_pow]
  calc ((eigenProj B t).map σ)ᵀ
      = (1 + σ (t ^ 2) • B.map σ + σ t • (B.map σ) ^ 2)ᵀ := by rw [hmap]
    _ = 1 + σ (t ^ 2) • (B.map σ)ᵀ + σ t • ((B.map σ)ᵀ) ^ 2 := by
        simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_pow,
          Matrix.transpose_one]
    _ = 1 + σ (t ^ 2) • B ^ 2 + σ t • (B ^ 2) ^ 2 := by rw [hBinv]
    _ = eigenProj B (t ^ 2) := by
        rw [map_pow, hσ, eigenProj,
          show (t ^ 2) ^ 2 = t by rw [← pow_mul]; exact ht4,
          show (B ^ 2) ^ 2 = B by rw [← pow_mul]; exact hB4]
        abel

end CFSG.LieType.SemisimpleCentralizers.OrderThree
