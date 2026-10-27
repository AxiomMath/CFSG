module

public import CFSG.CGT.Stroth77.Extension218Torus

public section

namespace CFSG.CGT.Stroth77

namespace Ext218

open Matrix

variable {s : ℕ} {i F G : ℤ}

theorem cS_eq_t221 : cS (Type221.k s) = (2 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 0 +
    (0 : ℤ) • gen (Type221.k s) 1 + (0 : ℤ) • gen (Type221.k s) 2 := by
  simp only [cS, zero_smul, add_zero]
  congr 1
  show (2 : ℤ) ^ (s + 2 - 1) = 2 * 2 ^ s
  rw [show s + 2 - 1 = s + 1 by omega, pow_succ]
  ring

theorem aS_eq_t221 : aS (Type221.k s) = (0 : ℤ) • gen (Type221.k s) 0 +
    (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 + (0 : ℤ) • gen (Type221.k s) 2 := by
  simp only [aS, zero_smul, add_zero, zero_add]
  congr 1
  show (2 : ℤ) ^ (s + 4 - 1) = 8 * 2 ^ s
  rw [show s + 4 - 1 = s + 3 by omega, pow_add]
  ring

theorem bS_eq_t221 : bS (Type221.k s) = (0 : ℤ) • gen (Type221.k s) 0 +
    (0 : ℤ) • gen (Type221.k s) 1 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2 := by
  simp only [bS, zero_smul, zero_add]
  congr 1
  show (2 : ℤ) ^ (s + 4 - 1) = 8 * 2 ^ s
  rw [show s + 4 - 1 = s + 3 by omega, pow_add]
  ring

@[expose] def baseU221 (s : ℕ) : Torus (Type221.k s) :=
  (-1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 + (0 : ℤ) • gen (Type221.k s) 2

@[expose] def baseT221 (s : ℕ) (G : ℤ) : Torus (Type221.k s) :=
  (-4 * G - 8 : ℤ) • gen (Type221.k s) 0 + (2 : ℤ) • gen (Type221.k s) 1 +
    (4 : ℤ) • gen (Type221.k s) 2

@[expose] def baseUV221 (s : ℕ) (G : ℤ) : Torus (Type221.k s) :=
  (-4 * G - 10 : ℤ) • gen (Type221.k s) 0 + (2 : ℤ) • gen (Type221.k s) 1 +
    (-2 : ℤ) • gen (Type221.k s) 2

@[expose] def bv221 (s : ℕ) (x y z : ℕ) : Torus (Type221.k s) :=
  x • cS (Type221.k s) + y • aS (Type221.k s) + z • bS (Type221.k s)

theorem bv221_add (x y z x' y' z' : ℕ) :
    bv221 s x y z + bv221 s x' y' z' = bv221 s (x + x') (y + y') (z + z') := by
  simp only [bv221, add_smul]
  abel

theorem bv221_eq_iff (x y z x' y' z' : ℕ) :
    bv221 s x y z = bv221 s x' y' z' ↔ x % 2 = x' % 2 ∧ y % 2 = y' % 2 ∧ z % 2 = z' % 2 :=
  bits_eq_iff (by change 1 ≤ s + 2; omega) (by change 1 ≤ s + 4; omega)
    (by change 1 ≤ s + 4; omega) x y z x' y' z'

theorem bv221_zero : bv221 s 0 0 0 = 0 := by
  simp [bv221]

theorem two_smul_bv221 (x y z : ℕ) : (2 : ℤ) • bv221 s x y z = 0 := by
  have h := (bv221_eq_iff (s := s) (x + x) (y + y) (z + z) 0 0 0).mpr
    ⟨by omega, by omega, by omega⟩
  rw [two_zsmul, bv221_add, h, bv221_zero]

theorem phiU_gen0_sub_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φu (gen (Type221.k s) 0) - gen (Type221.k s) 0 =
      (2 : ℤ) • baseU221 s := by
  conv_lhs => rw [show gen (Type221.k s) 0 = (1 : ℤ) • gen (Type221.k s) 0 +
    (0 : ℤ) • gen (Type221.k s) 1 + (0 : ℤ) • gen (Type221.k s) 2 by simp]
  rw [phiU_gen0_t221 h, baseU221]
  module

theorem phiR_gen0_sub_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φρ (gen (Type221.k s) 0) - gen (Type221.k s) 0 =
      (2 : ℤ) • (0 : Torus (Type221.k s)) := by
  conv_lhs => rw [show gen (Type221.k s) 0 = (1 : ℤ) • gen (Type221.k s) 0 +
    (0 : ℤ) • gen (Type221.k s) 1 + (0 : ℤ) • gen (Type221.k s) 2 by simp]
  rw [phiR_gen0_t221 h]
  module

theorem phiT_gen0_sub_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φt (gen (Type221.k s) 0) - gen (Type221.k s) 0 =
      (2 : ℤ) • baseT221 s G := by
  conv_lhs => rw [show gen (Type221.k s) 0 = (1 : ℤ) • gen (Type221.k s) 0 +
    (0 : ℤ) • gen (Type221.k s) 1 + (0 : ℤ) • gen (Type221.k s) 2 by simp]
  rw [phiT_gen0_t221 h, baseT221]
  module

theorem phiUV_gen0_sub_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φuv (gen (Type221.k s) 0) - gen (Type221.k s) 0 =
      (2 : ℤ) • baseUV221 s G := by
  conv_lhs => rw [show gen (Type221.k s) 0 = (1 : ℤ) • gen (Type221.k s) 0 +
    (0 : ℤ) • gen (Type221.k s) 1 + (0 : ℤ) • gen (Type221.k s) 2 by simp]
  rw [phiUV_gen0_t221 h, baseUV221]
  module

theorem phiR_bits_t221 (h : Type221.Data s i F G) (x y z : ℕ) :
    (Type221.action h).φρ (bv221 s x y z) = bv221 s x z (y + z) := by
  have h1 : (Type221.action h).φρ (cS (Type221.k s)) = cS (Type221.k s) := by
    conv_lhs => rw [cS_eq_t221]
    rw [phiR_cS_t221 h, cS_eq_t221]
  have h2 : (Type221.action h).φρ (aS (Type221.k s)) = bS (Type221.k s) := by
    conv_lhs => rw [aS_eq_t221]
    rw [phiR_aS_t221 h, bS_eq_t221]
  have h3 : (Type221.action h).φρ (bS (Type221.k s)) = aS (Type221.k s) + bS (Type221.k s) := by
    conv_lhs => rw [bS_eq_t221]
    rw [phiR_bS_t221 h, aS_eq_t221, bS_eq_t221]
    module
  simp only [bv221, map_add, map_nsmul, h1, h2, h3, smul_add, add_smul]
  abel

theorem phiU_bits_t221 (h : Type221.Data s i F G) (x y z : ℕ) :
    (Type221.action h).φu (bv221 s x y z) = bv221 s x z y := by
  have h1 : (Type221.action h).φu (cS (Type221.k s)) = cS (Type221.k s) := by
    conv_lhs => rw [cS_eq_t221]
    rw [phiU_cS_t221 h, cS_eq_t221]
  have h2 : (Type221.action h).φu (aS (Type221.k s)) = bS (Type221.k s) := by
    conv_lhs => rw [aS_eq_t221]
    rw [phiU_aS_t221 h, bS_eq_t221]
  have h3 : (Type221.action h).φu (bS (Type221.k s)) = aS (Type221.k s) := by
    conv_lhs => rw [bS_eq_t221]
    rw [phiU_bS_t221 h, aS_eq_t221]
  simp only [bv221, map_add, map_nsmul, h1, h2, h3]
  abel

theorem phiT_bits_t221 (h : Type221.Data s i F G) (x y z : ℕ) :
    (Type221.action h).φt (bv221 s x y z) = bv221 s x (x + y) z := by
  have h1 : (Type221.action h).φt (cS (Type221.k s)) = cS (Type221.k s) + aS (Type221.k s) := by
    conv_lhs => rw [cS_eq_t221]
    rw [phiT_cS_t221 h, aS_eq_t221, cS_eq_t221]
    module
  have h2 : (Type221.action h).φt (aS (Type221.k s)) = aS (Type221.k s) := by
    conv_lhs => rw [aS_eq_t221]
    rw [phiT_aS_t221 h, aS_eq_t221]
  have h3 : (Type221.action h).φt (bS (Type221.k s)) = bS (Type221.k s) := by
    conv_lhs => rw [bS_eq_t221]
    rw [phiT_bS_t221 h, bS_eq_t221]
  simp only [bv221, map_add, map_nsmul, h1, h2, h3, smul_add, add_smul]
  abel

theorem phiUV_bits_t221 (h : Type221.Data s i F G) (x y z : ℕ) :
    (Type221.action h).φuv (bv221 s x y z) = bv221 s x (x + y) (x + z) := by
  have h1 : (Type221.action h).φuv (cS (Type221.k s)) =
      cS (Type221.k s) + aS (Type221.k s) + bS (Type221.k s) := by
    conv_lhs => rw [cS_eq_t221]
    rw [phiUV_cS_t221 h, aS_eq_t221, bS_eq_t221, cS_eq_t221]
    module
  have h2 : (Type221.action h).φuv (aS (Type221.k s)) = aS (Type221.k s) := by
    conv_lhs => rw [aS_eq_t221]
    rw [phiUV_aS_t221 h, aS_eq_t221]
  have h3 : (Type221.action h).φuv (bS (Type221.k s)) = bS (Type221.k s) := by
    conv_lhs => rw [bS_eq_t221]
    rw [phiUV_bS_t221 h, bS_eq_t221]
  simp only [bv221, map_add, map_nsmul, h1, h2, h3, smul_add, add_smul]
  abel

theorem bits_of_relations_t221 (h : Type221.Data s i F G)
    {xu yu zu xr yr zr xt yt zt xv yv zv : ℕ}
    (E1 : (baseU221 s + bv221 s xu yu zu) +
      (Type221.action h).φu (baseU221 s + bv221 s xu yu zu) = 0)
    (E2 : bv221 s xr yr zr + (Type221.action h).φρ (bv221 s xr yr zr) +
      (Type221.action h).φρ ((Type221.action h).φρ (bv221 s xr yr zr)) = 0)
    (E3 : (baseUV221 s G + bv221 s xv yv zv) +
      (Type221.action h).φuv (baseUV221 s G + bv221 s xv yv zv) = 0)
    (E4 : (baseT221 s G + bv221 s xt yt zt) +
      (Type221.action h).φt (baseT221 s G + bv221 s xt yt zt) = 0)
    (E5 : bv221 s xr yr zr + (Type221.action h).φρ (baseU221 s + bv221 s xu yu zu) +
      (Type221.action h).φρ ((Type221.action h).φu (bv221 s xr yr zr)) +
      (Type221.action h).φρ ((Type221.action h).φu
        ((Type221.action h).φρ (baseU221 s + bv221 s xu yu zu))) = 0)
    (E6 : (baseU221 s + bv221 s xu yu zu) +
      (Type221.action h).φu (baseUV221 s G + bv221 s xv yv zv) =
      (baseUV221 s G + bv221 s xv yv zv) +
        (Type221.action h).φuv (baseU221 s + bv221 s xu yu zu))
    (E7 : bv221 s xr yr zr + (Type221.action h).φρ (baseT221 s G + bv221 s xt yt zt) =
      (baseT221 s G + bv221 s xt yt zt) +
        (Type221.action h).φt (baseUV221 s G + bv221 s xv yv zv) +
        (Type221.action h).φt ((Type221.action h).φuv (bv221 s xr yr zr))) :
    (yu + zu) % 2 = 0 ∧ xr % 2 = 0 ∧ xv % 2 = 0 ∧ xt % 2 = 0 ∧ (zu + yr) % 2 = 0 ∧
      (xu + yv + zv) % 2 = 0 ∧ (yt + zv) % 2 = 0 ∧ (zt + yt + yv) % 2 = 0 := by
  have hU := phiU_baseU_t221 h
  have hR := phiR_baseU_t221 h
  have hR1 := phiR_gen0_t221 h
  have hUVb := phiUV_baseUV_t221 h
  have hTb := phiT_baseT_t221 h
  have hUUV := phiU_baseUV_t221 h
  have hUVU := phiUV_baseU_t221 h
  have hRT := phiR_baseT_t221 h
  have hTUV := phiT_baseUV_t221 h
  simp only [map_add] at E1 E3 E4 E5 E6 E7
  simp only [baseU221, baseT221, baseUV221] at E1 E3 E4 E5 E6 E7
  rw [hU] at E1
  rw [hUVb] at E3
  rw [hTb] at E4
  rw [hR, hU, hR1] at E5
  rw [hUUV, hUVU] at E6
  rw [hRT, hTUV] at E7
  set φu := (Type221.action h).φu with hφu
  set φρ := (Type221.action h).φρ with hφρ
  set φt := (Type221.action h).φt with hφt
  set φuv := (Type221.action h).φuv with hφuv
  have h1 : bv221 s xu yu zu + φu (bv221 s xu yu zu) = 0 := by
    linear_combination (norm := module) E1
  have h3 : bv221 s xv yv zv + φuv (bv221 s xv yv zv) = 0 := by
    linear_combination (norm := module) E3
  have h4 : bv221 s xt yt zt + φt (bv221 s xt yt zt) = 0 := by
    linear_combination (norm := module) E4
  have h5 : bv221 s xr yr zr + φρ (bv221 s xu yu zu) + φρ (φu (bv221 s xr yr zr)) +
      φρ (φu (φρ (bv221 s xu yu zu))) = 0 := by
    linear_combination (norm := module) E5
  have h6 : bv221 s xu yu zu + φu (bv221 s xv yv zv) =
      bv221 s xv yv zv + φuv (bv221 s xu yu zu) := by
    linear_combination (norm := module) E6
  have h7 : bv221 s xr yr zr + φρ (bv221 s xt yt zt) =
      bv221 s xt yt zt + φt (bv221 s xv yv zv) + φt (φuv (bv221 s xr yr zr)) := by
    linear_combination (norm := module) E7
  have h0 : (0 : Torus (Type221.k s)) = bv221 s 0 0 0 := by simp [bv221]
  rw [h0] at h1 h3 h4 h5 E2
  simp only [hφu, hφρ, hφt, hφuv, phiU_bits_t221, phiR_bits_t221, phiT_bits_t221,
    phiUV_bits_t221, bv221_add, bv221_eq_iff] at h1 E2 h3 h4 h5 h6 h7
  omega

theorem bv221_eq_gens (x y z : ℕ) :
    bv221 s x y z = ((x : ℤ) * (2 * 2 ^ s)) • gen (Type221.k s) 0 +
      ((y : ℤ) * (8 * 2 ^ s)) • gen (Type221.k s) 1 +
        ((z : ℤ) * (8 * 2 ^ s)) • gen (Type221.k s) 2 := by
  rw [bv221, cS_eq_t221, aS_eq_t221, bS_eq_t221]
  simp only [← natCast_zsmul]
  module

theorem adjust_bits_t221 (h : Type221.Data s i F G)
    {xu yu zu xr yr zr xt yt zt xv yv zv : ℕ}
    (H : (yu + zu) % 2 = 0 ∧ xr % 2 = 0 ∧ xv % 2 = 0 ∧ xt % 2 = 0 ∧ (zu + yr) % 2 = 0 ∧
      (xu + yv + zv) % 2 = 0 ∧ (yt + zv) % 2 = 0 ∧ (zt + yt + yv) % 2 = 0) :
    bv221 s zv zr (yr + zr) + bv221 s xu yu zu +
        (Type221.action h).φu (bv221 s zv zr (yr + zr)) = bv221 s xu 0 0 ∧
      bv221 s zv zr (yr + zr) + bv221 s xr yr zr +
        (Type221.action h).φρ (bv221 s zv zr (yr + zr)) = bv221 s 0 0 0 ∧
      bv221 s zv zr (yr + zr) + bv221 s xt yt zt +
        (Type221.action h).φt (bv221 s zv zr (yr + zr)) = bv221 s 0 0 xu ∧
      bv221 s zv zr (yr + zr) + bv221 s xv yv zv +
        (Type221.action h).φuv (bv221 s zv zr (yr + zr)) = bv221 s 0 xu 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
  rw [phiU_bits_t221 h, phiR_bits_t221 h, phiT_bits_t221 h, phiUV_bits_t221 h]
  simp only [bv221_add, bv221_eq_iff]
  omega

theorem baseU_one_t221 :
    baseU221 s + bv221 s 1 0 0 = (-1 + 2 * 2 ^ s : ℤ) • gen (Type221.k s) 0 +
      (0 : ℤ) • gen (Type221.k s) 1 + (0 : ℤ) • gen (Type221.k s) 2 := by
  rw [baseU221, bv221_eq_gens]
  push_cast
  module

theorem baseT_one_t221 :
    baseT221 s G + bv221 s 0 0 1 = (-4 * G - 8 : ℤ) • gen (Type221.k s) 0 +
      (2 : ℤ) • gen (Type221.k s) 1 + (4 + 8 * 2 ^ s : ℤ) • gen (Type221.k s) 2 := by
  rw [baseT221, bv221_eq_gens]
  push_cast
  module

theorem baseUV_one_t221 :
    baseUV221 s G + bv221 s 0 1 0 = (-4 * G - 10 : ℤ) • gen (Type221.k s) 0 +
      (2 + 8 * 2 ^ s : ℤ) • gen (Type221.k s) 1 + (-2 : ℤ) • gen (Type221.k s) 2 := by
  rw [baseUV221, bv221_eq_gens]
  push_cast
  module

theorem zero_eq_gens_t221 :
    (0 : Torus (Type221.k s)) = (0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
      (0 : ℤ) • gen (Type221.k s) 2 := by
  simp

end Ext218

end CFSG.CGT.Stroth77
