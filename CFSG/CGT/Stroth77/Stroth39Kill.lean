module

public import CFSG.CGT.Stroth77.Stroth34Coord
public import CFSG.CGT.Stroth77.Types321
public import CFSG.CGT.Stroth77.Extension24Basic
public import CFSG.CGT.Stroth77.Extension22Cocycle
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Stroth77.Extension22FourC4
public import CFSG.CGT.Stroth77.TorusCard
public import CFSG.Foundations
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.CGT.Stroth77

namespace Type321

local notation "g0" => gen Type321.k 0
local notation "g1" => gen Type321.k 1
local notation "g2" => gen Type321.k 2

private theorem uvM_eq (i j : Fin 3) :
    Type321.uvM i j = (!![-3, 4, 84; 1, 1, 22; -1, 6, -7] : IntMat) i j := by
  fin_cases i <;> fin_cases j <;> simp [Type321.uvM, Type321.uvA, Type321.tM, Type321.ρM,
    ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply]

private theorem tM_eq (i j : Fin 3) :
    Type321.tM i j = (!![1, 0, 28; 1, 3, -6; 2, 0, -5] : IntMat) i j := by
  fin_cases i <;> fin_cases j <;> simp [Type321.uvM, Type321.uvA, Type321.tM, Type321.ρM,
    ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply]

private theorem ρM_eq (i j : Fin 3) :
    Type321.ρM i j = (!![1, 0, 4; 0, 0, -1; 0, 1, -1] : IntMat) i j := by
  fin_cases i <;> fin_cases j <;> simp [Type321.ρM, ofCols_apply]

theorem uv_gens (x y z : ℤ) : Type321.action.φuv (x • g0 + y • g1 + z • g2) =
    (-3 * x + 4 * y + 84 * z) • g0 + (x + y + 22 * z) • g1 + (-x + 6 * y - 7 * z) • g2 := by
  rw [show Type321.action.φuv = matAct Type321.k Type321.uvM Type321.compat_uv from rfl,
    matAct_zsmul_gens]
  simp only [uvM_eq]
  simp [Matrix.of_apply] <;> ring_nf

theorem t_gens (x y z : ℤ) : Type321.action.φt (x • g0 + y • g1 + z • g2) =
    (x + 28 * z) • g0 + (x + 3 * y - 6 * z) • g1 + (2 * x - 5 * z) • g2 := by
  rw [show Type321.action.φt = matAct Type321.k Type321.tM Type321.compat_t from rfl,
    matAct_zsmul_gens]
  simp only [tM_eq]
  simp [Matrix.of_apply] <;> ring_nf

theorem rho_gens (x y z : ℤ) : Type321.action.φρ (x • g0 + y • g1 + z • g2) =
    (x + 4 * z) • g0 + (-z) • g1 + (y - z) • g2 := by
  rw [show Type321.action.φρ = matAct Type321.k Type321.ρM Type321.compat_rho from rfl,
    matAct_zsmul_gens]
  simp only [ρM_eq]
  simp [Matrix.of_apply] <;> ring_nf

private theorem gens_sub (a b c a' b' c' : ℤ) :
    (a • g0 + b • g1 + c • g2) - (a' • g0 + b' • g1 + c' • g2) =
      (a - a') • g0 + (b - b') • g1 + (c - c') • g2 := by
  rw [sub_smul, sub_smul, sub_smul]
  abel

private theorem gens_zero : (0 : Torus Type321.k) = (0 : ℤ) • g0 + (0 : ℤ) • g1 + (0 : ℤ) • g2 := by
  simp

private theorem two_pow_k (i : Fin 3) : (2 : ℤ) ^ Type321.k i = 8 := by
  fin_cases i <;> simp [Type321.k]

private theorem dvd_of_eq {p q r p' q' r' : ℤ}
    (h : p • g0 + q • g1 + r • g2 = p' • g0 + q' • g1 + r' • g2) :
    (8 : ℤ) ∣ p' - p ∧ (8 : ℤ) ∣ q' - q ∧ (8 : ℤ) ∣ r' - r := by
  have := zsmul_gens_dvd_of_eq h
  simpa only [two_pow_k] using this

private theorem eq_of_dvd {p q r p' q' r' : ℤ} (h0 : (8 : ℤ) ∣ p' - p) (h1 : (8 : ℤ) ∣ q' - q)
    (h2 : (8 : ℤ) ∣ r' - r) : p • g0 + q • g1 + r • g2 = p' • g0 + q' • g1 + r' • g2 :=
  zsmul_gens_eq_of_dvd (by rw [two_pow_k]; exact h0) (by rw [two_pow_k]; exact h1)
    (by rw [two_pow_k]; exact h2)

private theorem coord_zero (p q r : ℤ) :
    (p • g0 + q • g1 + r • g2) 0 = 0 ↔ (8 : ℤ) ∣ p := by
  rw [zsmul_gens_apply_zero]
  have := ZMod.intCast_zmod_eq_zero_iff_dvd p (2 ^ Type321.k 0)
  rw [this]
  norm_num [Type321.k]

theorem kill (ruv rt d0 : Torus Type321.k)
    (h1 : ruv + Type321.action.φuv ruv = 0) (h2 : rt + Type321.action.φt rt = 0)
    (h3 : ruv + Type321.action.φuv rt = rt + Type321.action.φt ruv)
    (h4 : Type321.action.φρ (ruv + Type321.action.φuv rt) = ruv - d0 + Type321.action.φuv d0)
    (h5 : Type321.action.φρ ruv = rt - d0 + Type321.action.φt d0) :
    ∃ d : Torus Type321.k,
      (ruv - d + Type321.action.φuv d) 0 = 0 ∧
        (ruv - d + Type321.action.φuv d) + (ruv - d + Type321.action.φuv d) = 0 ∧
      (rt - d + Type321.action.φt d) 0 = 0 ∧
        (rt - d + Type321.action.φt d) + (rt - d + Type321.action.φt d) = 0 := by
  obtain ⟨a0, a1, a2, rfl⟩ := torus_eq_zsmul_gens _ ruv
  obtain ⟨b0, b1, b2, rfl⟩ := torus_eq_zsmul_gens _ rt
  obtain ⟨c0, c1, c2, rfl⟩ := torus_eq_zsmul_gens _ d0
  rw [uv_gens, gens_add, gens_zero] at h1
  rw [t_gens, gens_add, gens_zero] at h2
  rw [uv_gens, t_gens, gens_add, gens_add] at h3
  rw [uv_gens, gens_add, rho_gens, uv_gens, gens_sub, gens_add] at h4
  rw [rho_gens, t_gens, gens_sub, gens_add] at h5
  obtain ⟨⟨k10, e10⟩, ⟨k11, e11⟩, ⟨k12, e12⟩⟩ := dvd_of_eq h1
  obtain ⟨⟨k20, e20⟩, ⟨k21, e21⟩, ⟨k22, e22⟩⟩ := dvd_of_eq h2
  obtain ⟨⟨k30, e30⟩, ⟨k31, e31⟩, ⟨k32, e32⟩⟩ := dvd_of_eq h3
  obtain ⟨⟨k40, e40⟩, ⟨k41, e41⟩, ⟨k42, e42⟩⟩ := dvd_of_eq h4
  obtain ⟨⟨k50, e50⟩, ⟨k51, e51⟩, ⟨k52, e52⟩⟩ := dvd_of_eq h5
  refine ⟨(3 * a1 + a2 + b1) • g0 + c2 • g1 + (c1 + c2) • g2, ?_⟩
  rw [uv_gens, t_gens, gens_sub, gens_sub, gens_add, gens_add, gens_add, gens_add, coord_zero,
    coord_zero, gens_zero]
  refine ⟨⟨(1) * k11 + (3) * k20 + (1) * k21 + (-3) * k32 + (-2) * k41
      + (2) * k51 + (1) * a0 + (-1) * a1 + (-1) * b1 + (18) * c2
      + (10) * c1 + (1) * b0 + (11) * b2,
      by linear_combination (1) * e11 + (3) * e20 + (1) * e21 + (-3) * e32 + (-2) * e41
        + (2) * e51⟩,
    eq_of_dvd ⟨(-2) * k11 + (2) * k20 + (-2) * k21 + (-2) * k32 + (-4) * k41
      + (-4) * k51 + (3) * a1 + (-5) * a2 + (2) * b1 + (-14) * c2
      + (-20) * c1 + (7) * b2 + (1) * c0,
      by linear_combination (-2) * e11 + (2) * e20 + (-2) * e21 + (-2) * e32 + (-4) * e41
        + (-4) * e51⟩
      ⟨(2) * k20 + (2) * k21 + (-3) * k30 + (-4) * k40 + (-2) * k41
      + (-2) * k42 + (-1) * a1 + (40) * c2 + (9) * a2 + (-12) * b1
      + (-2) * c1 + (5) * b0 + (-63) * b2 + (-2) * c0,
      by linear_combination (2) * e20 + (2) * e21 + (-3) * e30 + (-4) * e40 + (-2) * e41
        + (-2) * e42⟩
      ⟨(2) * k11 + (-1) * k20 + (3) * k21 + (2) * k30 + (1) * k32
      + (-4) * k40 + (-2) * k42 + (-2) * k51 + (6) * c1 + (39) * c2
      + (1) * a1 + (-9) * b1 + (-2) * a2 + (2) * b0 + (-21) * b2
      + (-2) * c0,
      by linear_combination (2) * e11 + (-1) * e20 + (3) * e21 + (2) * e30 + (1) * e32
        + (-4) * e40 + (-2) * e42 + (-2) * e51⟩,
    ⟨(2) * k11 + (3) * k20 + (-4) * k21 + (2) * k30 + (-3) * k32
      + (-4) * k40 + (2) * k41 + (-2) * k42 + (-4) * k51 + (3) * b0
      + (8) * c1 + (35) * c2 + (1) * a0 + (-5) * a2 + (4) * b2
      + (-17) * b1 + (-2) * c0,
      by linear_combination (2) * e11 + (3) * e20 + (-4) * e21 + (2) * e30 + (-3) * e32
        + (-4) * e40 + (2) * e41 + (-2) * e42 + (-4) * e51⟩,
    eq_of_dvd ⟨(-4) * k11 + (2) * k20 + (-4) * k30 + (-2) * k32 + (-4) * k41
      + (-4) * k42 + (1) * b0 + (-4) * c1 + (-1) * a1 + (3) * a2
      + (-51) * b2 + (2) * b1,
      by linear_combination (-4) * e11 + (2) * e20 + (-4) * e30 + (-2) * e32 + (-4) * e41
        + (-4) * e42⟩
      ⟨(2) * k11 + (-1) * k20 + (1) * k21 + (-2) * k30 + (-3) * k32
      + (-2) * k41 + (2) * k51 + (-2) * b1 + (8) * c2 + (10) * a2
      + (1) * c1 + (1) * a0 + (1) * b0 + (-24) * b2,
      by linear_combination (2) * e11 + (-1) * e20 + (1) * e21 + (-2) * e30 + (-3) * e32
        + (-2) * e41 + (2) * e51⟩
      ⟨(2) * k11 + (-3) * k20 + (-3) * k21 + (3) * k30 + (1) * k32
      + (-4) * k40 + (-2) * k41 + (-2) * k42 + (-15) * b2 + (5) * c1
      + (47) * c2 + (-1) * a1 + (-6) * a2 + (-11) * b1 + (-2) * c0,
      by linear_combination (2) * e11 + (-3) * e20 + (-3) * e21 + (3) * e30 + (1) * e32
        + (-4) * e40 + (-2) * e41 + (-2) * e42⟩⟩

theorem rho_orbit (v w : Torus Type321.k) (hv2 : v + v = 0) (hv0 : v ≠ 0)
    (hρ : Type321.action.φρ (Type321.action.φρ v) = v + Type321.action.φρ v) (hw0 : w 0 = 0)
    (hw2 : w + w = 0) :
    w = 0 ∨ w = v ∨ w = Type321.action.φρ v ∨ w = v + Type321.action.φρ v := by
  obtain ⟨x, y, z, rfl⟩ := torus_eq_zsmul_gens _ v
  obtain ⟨p, q, r, rfl⟩ := torus_eq_zsmul_gens _ w
  rw [gens_add, gens_zero] at hv2 hw2
  rw [rho_gens, rho_gens, gens_add] at hρ
  rw [coord_zero] at hw0
  obtain ⟨v0, v1, v2⟩ := dvd_of_eq hv2
  obtain ⟨w1, w2', w3⟩ := dvd_of_eq hw2
  obtain ⟨r0, r1, r2⟩ := dvd_of_eq hρ
  have hv : ¬ ((8 : ℤ) ∣ x ∧ (8 : ℤ) ∣ y ∧ (8 : ℤ) ∣ z) := fun ⟨a, b, c⟩ => hv0 (by
    rw [gens_zero]
    exact eq_of_dvd (by omega) (by omega) (by omega))
  rw [rho_gens, gens_add]
  obtain ⟨X, rfl⟩ : (4 : ℤ) ∣ x := by omega
  obtain ⟨Y, rfl⟩ : (4 : ℤ) ∣ y := by omega
  obtain ⟨Z, rfl⟩ : (4 : ℤ) ∣ z := by omega
  obtain ⟨Q, rfl⟩ : (4 : ℤ) ∣ q := by omega
  obtain ⟨P, rfl⟩ : (4 : ℤ) ∣ r := by omega
  rcases Int.even_or_odd Y with ⟨Y', rfl⟩ | ⟨Y', rfl⟩ <;>
  rcases Int.even_or_odd Z with ⟨Z', rfl⟩ | ⟨Z', rfl⟩ <;>
  rcases Int.even_or_odd Q with ⟨Q', rfl⟩ | ⟨Q', rfl⟩ <;>
  rcases Int.even_or_odd P with ⟨P', rfl⟩ | ⟨P', rfl⟩ <;>
  first
  | exact Or.inl ((eq_of_dvd (by omega) (by omega) (by omega)).trans gens_zero.symm)
  | exact Or.inr (Or.inl (eq_of_dvd (by omega) (by omega) (by omega)))
  | exact Or.inr (Or.inr (Or.inl (eq_of_dvd (by omega) (by omega) (by omega))))
  | exact Or.inr (Or.inr (Or.inr (eq_of_dvd (by omega) (by omega) (by omega))))
  | (exfalso; omega)

end Type321

namespace Type331

local notation "g0" => gen Type331.k 0
local notation "g1" => gen Type331.k 1
local notation "g2" => gen Type331.k 2

private theorem uvM_eq (i j : Fin 3) :
    Type331.uvM i j = (!![-3, 4, 20; 5, 1, 38; -1, 6, 9] : IntMat) i j := by
  fin_cases i <;> fin_cases j <;> simp [Type331.uvM, Type331.uvA, Type331.tM, Type331.ρM,
    ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply]

private theorem tM_eq (i j : Fin 3) :
    Type331.tM i j = (!![1, 0, 28; 1, 3, -6; -2, 0, -5] : IntMat) i j := by
  fin_cases i <;> fin_cases j <;> simp [Type331.uvM, Type331.uvA, Type331.tM, Type331.ρM,
    ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply]

private theorem ρM_eq (i j : Fin 3) :
    Type331.ρM i j = (!![1, 0, 4; 0, 0, -1; 0, 1, -1] : IntMat) i j := by
  fin_cases i <;> fin_cases j <;> simp [Type331.ρM, ofCols_apply]

theorem uv_gens (x y z : ℤ) : Type331.action.φuv (x • g0 + y • g1 + z • g2) =
    (-3 * x + 4 * y + 20 * z) • g0 + (5 * x + y + 38 * z) • g1 + (-x + 6 * y + 9 * z) • g2 := by
  rw [show Type331.action.φuv = matAct Type331.k Type331.uvM Type331.compat_uv from rfl,
    matAct_zsmul_gens]
  simp only [uvM_eq]
  simp [Matrix.of_apply] <;> ring_nf

theorem t_gens (x y z : ℤ) : Type331.action.φt (x • g0 + y • g1 + z • g2) =
    (x + 28 * z) • g0 + (x + 3 * y - 6 * z) • g1 + (-2 * x - 5 * z) • g2 := by
  rw [show Type331.action.φt = matAct Type331.k Type331.tM Type331.compat_t from rfl,
    matAct_zsmul_gens]
  simp only [tM_eq]
  simp [Matrix.of_apply] <;> ring_nf

theorem rho_gens (x y z : ℤ) : Type331.action.φρ (x • g0 + y • g1 + z • g2) =
    (x + 4 * z) • g0 + (-z) • g1 + (y - z) • g2 := by
  rw [show Type331.action.φρ = matAct Type331.k Type331.ρM Type331.compat_rho from rfl,
    matAct_zsmul_gens]
  simp only [ρM_eq]
  simp [Matrix.of_apply] <;> ring_nf

private theorem gens_sub (a b c a' b' c' : ℤ) :
    (a • g0 + b • g1 + c • g2) - (a' • g0 + b' • g1 + c' • g2) =
      (a - a') • g0 + (b - b') • g1 + (c - c') • g2 := by
  rw [sub_smul, sub_smul, sub_smul]
  abel

private theorem gens_zero : (0 : Torus Type331.k) = (0 : ℤ) • g0 + (0 : ℤ) • g1 + (0 : ℤ) • g2 := by
  simp

private theorem two_pow_k (i : Fin 3) : (2 : ℤ) ^ Type331.k i = 8 := by
  fin_cases i <;> simp [Type331.k]

private theorem dvd_of_eq {p q r p' q' r' : ℤ}
    (h : p • g0 + q • g1 + r • g2 = p' • g0 + q' • g1 + r' • g2) :
    (8 : ℤ) ∣ p' - p ∧ (8 : ℤ) ∣ q' - q ∧ (8 : ℤ) ∣ r' - r := by
  have := zsmul_gens_dvd_of_eq h
  simpa only [two_pow_k] using this

private theorem eq_of_dvd {p q r p' q' r' : ℤ} (h0 : (8 : ℤ) ∣ p' - p) (h1 : (8 : ℤ) ∣ q' - q)
    (h2 : (8 : ℤ) ∣ r' - r) : p • g0 + q • g1 + r • g2 = p' • g0 + q' • g1 + r' • g2 :=
  zsmul_gens_eq_of_dvd (by rw [two_pow_k]; exact h0) (by rw [two_pow_k]; exact h1)
    (by rw [two_pow_k]; exact h2)

private theorem coord_zero (p q r : ℤ) :
    (p • g0 + q • g1 + r • g2) 0 = 0 ↔ (8 : ℤ) ∣ p := by
  rw [zsmul_gens_apply_zero]
  have := ZMod.intCast_zmod_eq_zero_iff_dvd p (2 ^ Type331.k 0)
  rw [this]
  norm_num [Type331.k]

theorem kill (ruv rt d0 : Torus Type331.k)
    (h1 : ruv + Type331.action.φuv ruv = 0) (h2 : rt + Type331.action.φt rt = 0)
    (h3 : ruv + Type331.action.φuv rt = rt + Type331.action.φt ruv)
    (h4 : Type331.action.φρ (ruv + Type331.action.φuv rt) = ruv - d0 + Type331.action.φuv d0)
    (h5 : Type331.action.φρ ruv = rt - d0 + Type331.action.φt d0) :
    ∃ d : Torus Type331.k,
      (ruv - d + Type331.action.φuv d) 0 = 0 ∧
        (ruv - d + Type331.action.φuv d) + (ruv - d + Type331.action.φuv d) = 0 ∧
      (rt - d + Type331.action.φt d) 0 = 0 ∧
        (rt - d + Type331.action.φt d) + (rt - d + Type331.action.φt d) = 0 := by
  obtain ⟨a0, a1, a2, rfl⟩ := torus_eq_zsmul_gens _ ruv
  obtain ⟨b0, b1, b2, rfl⟩ := torus_eq_zsmul_gens _ rt
  obtain ⟨c0, c1, c2, rfl⟩ := torus_eq_zsmul_gens _ d0
  rw [uv_gens, gens_add, gens_zero] at h1
  rw [t_gens, gens_add, gens_zero] at h2
  rw [uv_gens, t_gens, gens_add, gens_add] at h3
  rw [uv_gens, gens_add, rho_gens, uv_gens, gens_sub, gens_add] at h4
  rw [rho_gens, t_gens, gens_sub, gens_add] at h5
  obtain ⟨⟨k10, e10⟩, ⟨k11, e11⟩, ⟨k12, e12⟩⟩ := dvd_of_eq h1
  obtain ⟨⟨k20, e20⟩, ⟨k21, e21⟩, ⟨k22, e22⟩⟩ := dvd_of_eq h2
  obtain ⟨⟨k30, e30⟩, ⟨k31, e31⟩, ⟨k32, e32⟩⟩ := dvd_of_eq h3
  obtain ⟨⟨k40, e40⟩, ⟨k41, e41⟩, ⟨k42, e42⟩⟩ := dvd_of_eq h4
  obtain ⟨⟨k50, e50⟩, ⟨k51, e51⟩, ⟨k52, e52⟩⟩ := dvd_of_eq h5
  refine ⟨(3 * a1 + a2 + b1) • g0 + c2 • g1 + (c1 + c2) • g2, ?_⟩
  rw [uv_gens, t_gens, gens_sub, gens_sub, gens_add, gens_add, gens_add, gens_add, coord_zero,
    coord_zero, gens_zero]
  refine ⟨⟨(-1) * k12 + (1) * k20 + (-1) * k21 + (-3) * k30 + (3) * k32
      + (-2) * k41 + (2) * k51 + (1) * a0 + (-2) * a1 + (11) * a2
      + (1) * b1 + (14) * c2 + (2) * c1 + (1) * b0 + (2) * b2 + (1) * c0,
      by linear_combination (-1) * e12 + (1) * e20 + (-1) * e21 + (-3) * e30 + (3) * e32
        + (-2) * e41 + (2) * e51⟩,
    eq_of_dvd ⟨(2) * k12 + (-2) * k20 + (2) * k21 + (-2) * k30 + (2) * k32
      + (-4) * k41 + (-4) * k51 + (5) * a1 + (13) * a2 + (6) * b1
      + (10) * c2 + (-4) * c1 + (-7) * b2 + (3) * c0,
      by linear_combination (2) * e12 + (-2) * e20 + (2) * e21 + (-2) * e30 + (2) * e32
        + (-4) * e41 + (-4) * e51⟩
      ⟨(2) * k12 + (-4) * k20 + (-2) * k21 + (2) * k30 + (2) * k31
      + (2) * k32 + (-2) * k41 + (-2) * k42 + (-3) * a1 + (2) * c2
      + (-2) * a2 + (3) * b1 + (-8) * c1 + (-3) * b0 + (-1) * b2
      + (1) * c0,
      by linear_combination (2) * e12 + (-4) * e20 + (-2) * e21 + (2) * e30 + (2) * e31
        + (2) * e32 + (-2) * e41 + (-2) * e42⟩
      ⟨(-1) * k20 + (1) * k21 + (-2) * k30 + (2) * k31 + (-3) * k32
      + (-2) * k42 + (-2) * k51 + (-3) * c2 + (-1) * b1 + (1) * b0
      + (-10) * b2 + (7) * a2 + (-1) * a0,
      by linear_combination (-1) * e20 + (1) * e21 + (-2) * e30 + (2) * e31 + (-3) * e32
        + (-2) * e42 + (-2) * e51⟩,
    ⟨(3) * k20 + (2) * k21 + (-2) * k30 + (2) * k31 + (1) * k32
      + (2) * k41 + (-2) * k42 + (-4) * k51 + (2) * b0 + (6) * c1
      + (-7) * c2 + (5) * b2 + (1) * b1 + (10) * a2 + (-1) * a1
      + (-1) * c0,
      by linear_combination (3) * e20 + (2) * e21 + (-2) * e30 + (2) * e31 + (1) * e32
        + (2) * e41 + (-2) * e42 + (-4) * e51⟩,
    eq_of_dvd ⟨(2) * k20 + (-4) * k21 + (-4) * k30 + (-4) * k31 + (-2) * k32
      + (-4) * k41 + (-4) * k42 + (-4) * b0 + (-4) * c1 + (16) * c2
      + (-31) * b2 + (11) * a2 + (1) * a1 + (2) * c0,
      by linear_combination (2) * e20 + (-4) * e21 + (-4) * e30 + (-4) * e31 + (-2) * e32
        + (-4) * e41 + (-4) * e42⟩
      ⟨(2) * k12 + (-3) * k20 + (-3) * k21 + (-3) * k32 + (-2) * k41
      + (2) * k51 + (-3) * b1 + (12) * c2 + (1) * a1 + (1) * c1
      + (-1) * a0 + (-1) * b0 + (-9) * b2 + (1) * c0,
      by linear_combination (2) * e12 + (-3) * e20 + (-3) * e21 + (-3) * e32 + (-2) * e41
        + (2) * e51⟩
      ⟨(-4) * k12 + (-3) * k20 + (1) * k21 + (-4) * k30 + (2) * k31
      + (-1) * k32 + (-2) * k41 + (-2) * k42 + (-18) * b2 + (3) * c1
      + (13) * c2 + (-2) * a1 + (11) * a2 + (1) * b1 + (1) * b0 + (1) * c0,
      by linear_combination (-4) * e12 + (-3) * e20 + (1) * e21 + (-4) * e30 + (2) * e31
        + (-1) * e32 + (-2) * e41 + (-2) * e42⟩⟩

theorem rho_orbit (v w : Torus Type331.k) (hv2 : v + v = 0) (hv0 : v ≠ 0)
    (hρ : Type331.action.φρ (Type331.action.φρ v) = v + Type331.action.φρ v) (hw0 : w 0 = 0)
    (hw2 : w + w = 0) :
    w = 0 ∨ w = v ∨ w = Type331.action.φρ v ∨ w = v + Type331.action.φρ v := by
  obtain ⟨x, y, z, rfl⟩ := torus_eq_zsmul_gens _ v
  obtain ⟨p, q, r, rfl⟩ := torus_eq_zsmul_gens _ w
  rw [gens_add, gens_zero] at hv2 hw2
  rw [rho_gens, rho_gens, gens_add] at hρ
  rw [coord_zero] at hw0
  obtain ⟨v0, v1, v2⟩ := dvd_of_eq hv2
  obtain ⟨w1, w2', w3⟩ := dvd_of_eq hw2
  obtain ⟨r0, r1, r2⟩ := dvd_of_eq hρ
  have hv : ¬ ((8 : ℤ) ∣ x ∧ (8 : ℤ) ∣ y ∧ (8 : ℤ) ∣ z) := fun ⟨a, b, c⟩ => hv0 (by
    rw [gens_zero]
    exact eq_of_dvd (by omega) (by omega) (by omega))
  rw [rho_gens, gens_add]
  obtain ⟨X, rfl⟩ : (4 : ℤ) ∣ x := by omega
  obtain ⟨Y, rfl⟩ : (4 : ℤ) ∣ y := by omega
  obtain ⟨Z, rfl⟩ : (4 : ℤ) ∣ z := by omega
  obtain ⟨Q, rfl⟩ : (4 : ℤ) ∣ q := by omega
  obtain ⟨P, rfl⟩ : (4 : ℤ) ∣ r := by omega
  rcases Int.even_or_odd Y with ⟨Y', rfl⟩ | ⟨Y', rfl⟩ <;>
  rcases Int.even_or_odd Z with ⟨Z', rfl⟩ | ⟨Z', rfl⟩ <;>
  rcases Int.even_or_odd Q with ⟨Q', rfl⟩ | ⟨Q', rfl⟩ <;>
  rcases Int.even_or_odd P with ⟨P', rfl⟩ | ⟨P', rfl⟩ <;>
  first
  | exact Or.inl ((eq_of_dvd (by omega) (by omega) (by omega)).trans gens_zero.symm)
  | exact Or.inr (Or.inl (eq_of_dvd (by omega) (by omega) (by omega)))
  | exact Or.inr (Or.inr (Or.inl (eq_of_dvd (by omega) (by omega) (by omega))))
  | exact Or.inr (Or.inr (Or.inr (eq_of_dvd (by omega) (by omega) (by omega))))
  | (exfalso; omega)

end Type331

theorem StrothFrame.IsD.mem_of_proj_rho_t321 {G : Type} [Group G] [Finite G] {F : StrothFrame G}
    {D : Subgroup G} {dD : StrothWeakTypeData D StrothTypeIndex.t321} (h : F.IsD D dD)
    (hS : Local.Setting (F.S : Subgroup G) D) {e d₀ : G} (he : e ∈ hS.R)
    (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D) (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) (hd₀ : d₀ ∈ D)
    (hp : hS.proj dD.ρ e = e * d₀) : e ∈ D := by
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj huv ht
  obtain ⟨s1, s2⟩ := h.rho_stable_crd hS he huv ht hd₀ hp
  obtain ⟨d, w1, w2, w3, w4⟩ := Type321.kill _ _ _ c1 c2 c3 s1 s2
  obtain ⟨dG, hdG, hcdG⟩ := exists_crdT_eq dD.e d
  obtain ⟨huv', cuv'⟩ := crdT_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj huv hdG
  obtain ⟨ht', ct'⟩ := crdT_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj ht hdG
  obtain ⟨x2, x0, xρ, hE⟩ := h.crd_x1
  have hR : e * dG ∈ hS.R := mul_mem he (hS.D_le_R hdG)
  have key : e * dG ∈ D := by
    refine h.mem_of_conj_mem_E (hS.R_le_S hR) (hS.R_le_centralizer_omega hR) ?_ ?_
    · refine hE _ huv' ?_
      rw [cuv', hcdG]
      exact Type321.rho_orbit _ _ x2 x0 xρ w1 w2
    · refine hE _ ht' ?_
      rw [ct', hcdG]
      exact Type321.rho_orbit _ _ x2 x0 xρ w3 w4
  have := mul_mem key (inv_mem hdG)
  simpa using this

theorem StrothFrame.IsD.mem_of_proj_rho_t331 {G : Type} [Group G] [Finite G] {F : StrothFrame G}
    {D : Subgroup G} {dD : StrothWeakTypeData D StrothTypeIndex.t331} (h : F.IsD D dD)
    (hS : Local.Setting (F.S : Subgroup G) D) {e d₀ : G} (he : e ∈ hS.R)
    (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D) (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) (hd₀ : d₀ ∈ D)
    (hp : hS.proj dD.ρ e = e * d₀) : e ∈ D := by
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj huv ht
  obtain ⟨s1, s2⟩ := h.rho_stable_crd hS he huv ht hd₀ hp
  obtain ⟨d, w1, w2, w3, w4⟩ := Type331.kill _ _ _ c1 c2 c3 s1 s2
  obtain ⟨dG, hdG, hcdG⟩ := exists_crdT_eq dD.e d
  obtain ⟨huv', cuv'⟩ := crdT_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj huv hdG
  obtain ⟨ht', ct'⟩ := crdT_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj ht hdG
  obtain ⟨x2, x0, xρ, hE⟩ := h.crd_x1
  have hR : e * dG ∈ hS.R := mul_mem he (hS.D_le_R hdG)
  have key : e * dG ∈ D := by
    refine h.mem_of_conj_mem_E (hS.R_le_S hR) (hS.R_le_centralizer_omega hR) ?_ ?_
    · refine hE _ huv' ?_
      rw [cuv', hcdG]
      exact Type331.rho_orbit _ _ x2 x0 xρ w1 w2
    · refine hE _ ht' ?_
      rw [ct', hcdG]
      exact Type331.rho_orbit _ _ x2 x0 xρ w3 w4
  have := mul_mem key (inv_mem hdG)
  simpa using this

end CFSG.CGT.Stroth77
