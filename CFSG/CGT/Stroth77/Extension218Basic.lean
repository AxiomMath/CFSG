module

public import CFSG.CGT.Stroth77.Extension22Final

public section

namespace CFSG.CGT.Stroth77

namespace Ext218

open Matrix

theorem gens_eq_of_three_pow {k : Fin 3 → ℕ} {a b c a' b' c' : ℤ} (d0 d1 d2 : ℕ)
    {t0 t1 t2 : ℤ}
    (h0 : (3 : ℤ) ^ d0 * (a - a') = 2 ^ k 0 * t0)
    (h1 : (3 : ℤ) ^ d1 * (b - b') = 2 ^ k 1 * t1)
    (h2 : (3 : ℤ) ^ d2 * (c - c') = 2 ^ k 2 * t2) :
    a • gen k 0 + b • gen k 1 + c • gen k 2 = a' • gen k 0 + b' • gen k 1 + c' • gen k 2 := by
  have key : ∀ (d e : ℕ) {x y t : ℤ}, (3 : ℤ) ^ d * (x - y) = 2 ^ e * t →
      ((2 : ℤ) ^ e) ∣ (x - y) := by
    intro d e x y t h
    have hcop : IsCoprime ((2 : ℤ) ^ e) ((3 : ℤ) ^ d) := by
      have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
      exact h23.pow_left.pow_right
    exact hcop.dvd_of_dvd_mul_left ⟨t, by linear_combination h⟩
  exact gens_eq_of_dvd (key d0 (k 0) h0) (key d1 (k 1) h1) (key d2 (k 2) h2)

theorem matAct_gens_eq {k : Fin 3 → ℕ} (M : IntMat) (hM : Compat k M) {x y z x' y' z' : ℤ}
    (d0 d1 d2 : ℕ) {t0 t1 t2 : ℤ}
    (h0 : (3 : ℤ) ^ d0 * (M 0 0 * x + M 0 1 * y + M 0 2 * z - x') = 2 ^ k 0 * t0)
    (h1 : (3 : ℤ) ^ d1 * (M 1 0 * x + M 1 1 * y + M 1 2 * z - y') = 2 ^ k 1 * t1)
    (h2 : (3 : ℤ) ^ d2 * (M 2 0 * x + M 2 1 * y + M 2 2 * z - z') = 2 ^ k 2 * t2) :
    matAct k M hM (x • gen k 0 + y • gen k 1 + z • gen k 2) =
      x' • gen k 0 + y' • gen k 1 + z' • gen k 2 := by
  rw [matAct_zsmul_gens]
  exact gens_eq_of_three_pow d0 d1 d2 h0 h1 h2

@[expose] def cS (k : Fin 3 → ℕ) : Torus k := ((2 : ℤ) ^ (k 0 - 1)) • gen k 0

@[expose] def aS (k : Fin 3 → ℕ) : Torus k := ((2 : ℤ) ^ (k 1 - 1)) • gen k 1

@[expose] def bS (k : Fin 3 → ℕ) : Torus k := ((2 : ℤ) ^ (k 2 - 1)) • gen k 2

theorem bits_eq_gens (k : Fin 3 → ℕ) (x y z : ℕ) :
    x • cS k + y • aS k + z • bS k =
      ((x : ℤ) * 2 ^ (k 0 - 1)) • gen k 0 + ((y : ℤ) * 2 ^ (k 1 - 1)) • gen k 1 +
        ((z : ℤ) * 2 ^ (k 2 - 1)) • gen k 2 := by
  simp only [cS, aS, bS, ← natCast_zsmul, smul_smul]

theorem cast_mul_two_pow_pred_eq_iff {e : ℕ} (he : 1 ≤ e) (x x' : ℕ) :
    (((x : ℤ) * 2 ^ (e - 1) : ℤ) : ZMod (2 ^ e)) = (((x' : ℤ) * 2 ^ (e - 1) : ℤ) : ZMod (2 ^ e)) ↔
      x % 2 = x' % 2 := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  rw [show f + 1 - 1 = f by omega, ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  rw [show (x' : ℤ) * 2 ^ f - (x : ℤ) * 2 ^ f = 2 ^ f * ((x' : ℤ) - x) by ring, pow_succ]
  rw [mul_dvd_mul_iff_left (by positivity : ((2 : ℤ) ^ f) ≠ 0)]
  omega

theorem bits_eq_iff {k : Fin 3 → ℕ} (hk0 : 1 ≤ k 0) (hk1 : 1 ≤ k 1) (hk2 : 1 ≤ k 2)
    (x y z x' y' z' : ℕ) :
    x • cS k + y • aS k + z • bS k = x' • cS k + y' • aS k + z' • bS k ↔
      x % 2 = x' % 2 ∧ y % 2 = y' % 2 ∧ z % 2 = z' % 2 := by
  rw [bits_eq_gens, bits_eq_gens]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (cast_mul_two_pow_pred_eq_iff hk0 x x').mp (gens_coord_zero h)
    · exact (cast_mul_two_pow_pred_eq_iff hk1 y y').mp (gens_coord_one h)
    · exact (cast_mul_two_pow_pred_eq_iff hk2 z z').mp (gens_coord_two h)
  · rintro ⟨h0, h1, h2⟩
    exact gens_eq_of_coord ((cast_mul_two_pow_pred_eq_iff hk0 x x').mpr h0)
      ((cast_mul_two_pow_pred_eq_iff hk1 y y').mpr h1)
      ((cast_mul_two_pow_pred_eq_iff hk2 z z').mpr h2)

theorem exists_bits_of_two_smul_eq_zero {k : Fin 3 → ℕ} (hk0 : 1 ≤ k 0) (hk1 : 1 ≤ k 1)
    (hk2 : 1 ≤ k 2) {ω : Torus k} (h : (2 : ℤ) • ω = 0) :
    ∃ x y z : ℕ, x ≤ 1 ∧ y ≤ 1 ∧ z ≤ 1 ∧ ω = x • cS k + y • aS k + z • bS k := by
  obtain ⟨a, b, c, hω⟩ := torus_eq_zsmul_gens k ω
  have h' := h
  rw [hω, zsmul_gens] at h'
  have h0 := gens_coord_zero_of_eq_zero h'
  have h1 := gens_coord_one_of_eq_zero h'
  have h2 := gens_coord_two_of_eq_zero h'
  push_cast at h0 h1 h2
  have pick : ∀ {e : ℕ} (he : 1 ≤ e) {w : ℤ}, (2 : ZMod (2 ^ e)) * (w : ZMod (2 ^ e)) = 0 →
      ∃ x : ℕ, x ≤ 1 ∧ (w : ZMod (2 ^ e)) = (((x : ℤ) * 2 ^ (e - 1) : ℤ) : ZMod (2 ^ e)) := by
    intro e he w hw
    rcases (zmod_two_mul_eq_zero_iff he (w : ZMod (2 ^ e))).1 hw with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · exact ⟨1, le_refl _, by rw [h]; push_cast; ring⟩
  obtain ⟨x, hx1, hx⟩ := pick hk0 h0
  obtain ⟨y, hy1, hy⟩ := pick hk1 h1
  obtain ⟨z, hz1, hz⟩ := pick hk2 h2
  refine ⟨x, y, z, hx1, hy1, hz1, ?_⟩
  rw [hω, bits_eq_gens]
  exact gens_eq_of_coord hx hy hz

end Ext218

end CFSG.CGT.Stroth77
