module

public import CFSG.CGT.Stroth77.Stroth39Kill
public import CFSG.CGT.Stroth77.Stroth3VCase
public import CFSG.CGT.Stroth77.Stroth39

public section

namespace CFSG.CGT.Stroth77

namespace Type321

local notation "g0" => gen Type321.k 0
local notation "g1" => gen Type321.k 1
local notation "g2" => gen Type321.k 2

private theorem two_pow_k' (i : Fin 3) : (2 : ℤ) ^ Type321.k i = 8 := by
  fin_cases i <;> simp [Type321.k]

private theorem dvd_of_eq' {p q r p' q' r' : ℤ}
    (h : p • g0 + q • g1 + r • g2 = p' • g0 + q' • g1 + r' • g2) :
    (8 : ℤ) ∣ p' - p ∧ (8 : ℤ) ∣ q' - q ∧ (8 : ℤ) ∣ r' - r := by
  have := zsmul_gens_dvd_of_eq h
  simpa only [two_pow_k'] using this

private theorem eq_of_dvd' {p q r p' q' r' : ℤ} (h0 : (8 : ℤ) ∣ p' - p) (h1 : (8 : ℤ) ∣ q' - q)
    (h2 : (8 : ℤ) ∣ r' - r) : p • g0 + q • g1 + r • g2 = p' • g0 + q' • g1 + r' • g2 :=
  zsmul_gens_eq_of_dvd (by rw [two_pow_k']; exact h0) (by rw [two_pow_k']; exact h1)
    (by rw [two_pow_k']; exact h2)

private theorem smul_gens' (n a b c : ℤ) :
    n • (a • g0 + b • g1 + c • g2) = (n * a) • g0 + (n * b) • g1 + (n * c) • g2 := by
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]

private theorem zero_gens' : (0 : Torus Type321.k) = (0 : ℤ) • g0 + (0 : ℤ) • g1 + (0 : ℤ) • g2 :=
    by
  simp

private theorem g0_gens : g0 = (1 : ℤ) • g0 + (0 : ℤ) • g1 + (0 : ℤ) • g2 := by simp

private theorem g1_gens : g1 = (0 : ℤ) • g0 + (1 : ℤ) • g1 + (0 : ℤ) • g2 := by simp

private theorem g2_gens : g2 = (0 : ℤ) • g0 + (0 : ℤ) • g1 + (1 : ℤ) • g2 := by simp

private theorem val_mod_two' (X : ℤ) :
    (((X : ZMod (2 ^ Type321.k 0)).val % 2 : ℕ) : ℤ) = X % 2 := by
  have h8 : (2 ^ Type321.k 0 : ℕ) = 8 := by simp [Type321.k]
  rw [Int.natCast_mod, ZMod.val_intCast, h8]
  push_cast
  exact Int.emod_emod_of_dvd X (by norm_num)

private theorem coord0' (p q r : ℤ) : (p • g0 + q • g1 + r • g2) 0 =
    ((p : ℤ) : ZMod (2 ^ Type321.k 0)) :=
  zsmul_gens_apply_zero p q r

theorem u_gens (x y z : ℤ) : Type321.action.φu (x • g0 + y • g1 + z • g2) =
    (-1 * x) • g0 + z • g1 + y • g2 := by
  rw [show Type321.action.φu = matAct Type321.k Type321.uM Type321.compat_u from rfl,
      matAct_zsmul_gens]
  have huM : ∀ i j, Type321.uM i j = (!![-1, 0, 0; 0, 0, 1; 0, 1, 0] : IntMat) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Type321.uM, uMat, ofCols_apply]
  simp only [huM]
  simp [Matrix.of_apply] <;> ring_nf

private theorem g1_cyc : g1 = (7 : ℤ) • Type321.action.φuv g0 + (4 : ℤ) • Type321.action.φt g0 +
    (1 : ℤ) • Type321.action.φuv (Type321.action.φt g0) := by
  conv_rhs => rw [g0_gens, uv_gens, t_gens, uv_gens, smul_gens', smul_gens', smul_gens',
    gens_add, gens_add]
  conv_lhs => rw [g1_gens]
  exact eq_of_dvd' (by norm_num) (by norm_num) (by norm_num)

private theorem g2_cyc : g2 = (1 : ℤ) • Type321.action.φuv g0 + (7 : ℤ) • Type321.action.φt g0 +
    (4 : ℤ) • Type321.action.φuv (Type321.action.φt g0) := by
  conv_rhs => rw [g0_gens, uv_gens, t_gens, uv_gens, smul_gens', smul_gens', smul_gens',
    gens_add, gens_add]
  conv_lhs => rw [g2_gens]
  exact eq_of_dvd' (by norm_num) (by norm_num) (by norm_num)

theorem classify (δ : Torus Type321.k →+ Torus Type321.k)
    (hU : ∀ x, δ (Type321.action.φuv x) = Type321.action.φuv (δ x))
    (hT : ∀ x, δ (Type321.action.φt x) = Type321.action.φt (δ x))
    (h2 : ∀ x, x + x = 0 → δ x = x) (hinv : ∀ x, δ (δ x) = x) :
    ∃ α : ℤ, Odd α ∧ ∃ w, InW w ∧ ∀ x, δ x = α • x + (x 0).val • w := by
  obtain ⟨A, B, C, hδ0⟩ := torus_eq_zsmul_gens _ (δ g0)
  have hcyc : ∀ (p q r : ℤ), δ (p • Type321.action.φuv g0 + q • Type321.action.φt g0 +
      r • Type321.action.φuv (Type321.action.φt g0)) =
      p • Type321.action.φuv (δ g0) + q • Type321.action.φt (δ g0) +
        r • Type321.action.φuv (Type321.action.φt (δ g0)) := fun p q r => by
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hU, hT, hU, hT]
  have hδ1 : δ g1 = ((152) * A + (40) * B + (172) * C) • g0 + ((57) * A + (22) * B +
      (42) * C) • g1 + ((-8) * A + (60) * B + (-98) * C) • g2 := by
    conv_lhs => rw [g1_cyc, hcyc, hδ0, uv_gens, t_gens, uv_gens, smul_gens', smul_gens',
      smul_gens', gens_add, gens_add]
    exact eq_of_dvd' ⟨0, by ring⟩ ⟨0, by ring⟩ ⟨0, by ring⟩
  have hδ2 : δ g2 = ((680) * A + (52) * B + (-1832) * C) • g0 + ((192) * A + (34) * B +
      (-372) * C) • g1 + ((-23) * A + (78) * B + (-158) * C) • g2 := by
    conv_lhs => rw [g2_cyc, hcyc, hδ0, uv_gens, t_gens, uv_gens, smul_gens', smul_gens',
      smul_gens', gens_add, gens_add]
    exact eq_of_dvd' ⟨0, by ring⟩ ⟨0, by ring⟩ ⟨0, by ring⟩
  have hi := hinv g0
  rw [hδ0, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hδ0, hδ1, hδ2, smul_gens',
    smul_gens', smul_gens', gens_add, gens_add] at hi
  conv at hi => rhs; rw [g0_gens]
  obtain ⟨i0, i1, i2⟩ := dvd_of_eq' hi
  have h4 := h2 ((4 : ℤ) • g0) (by
    rw [g0_gens, smul_gens', gens_add, zero_gens']
    exact eq_of_dvd' (by norm_num) (by norm_num) (by norm_num))
  rw [map_zsmul, hδ0, smul_gens'] at h4
  conv at h4 => rhs; rw [g0_gens, smul_gens']
  obtain ⟨p0, p1, p2⟩ := dvd_of_eq' h4
  have key : ∀ a b c : ZMod 8, 4 * 1 - 4 * a = 0 → 4 * 0 - 4 * b = 0 → 4 * 0 - 4 * c = 0 →
      1 - (a * a + b * ((152) * a + (40) * b + (172) * c) + c * ((680) * a + (52) * b +
          (-1832) * c)) = 0 → 0 - (a * b + b * ((57) * a + (22) * b + (42) * c) + c * ((192) * a +
          (34) * b + (-372) * c)) = 0 → 0 - (a * c + b * ((-8) * a + (60) * b + (-98) * c) +
          c * ((-23) * a + (78) * b + (-158) * c)) = 0 →
      2 * b = 0 ∧ 2 * c = 0 ∧ (152) * a + (40) * b + (172) * c = 0 ∧ (57) * a + (22) * b +
          (42) * c - a = 0 ∧ (-8) * a + (60) * b + (-98) * c = 0 ∧
        (680) * a + (52) * b + (-1832) * c = 0 ∧ (192) * a + (34) * b + (-372) * c = 0 ∧
            (-23) * a + (78) * b + (-158) * c - a = 0 := by
    decide
  have cast0 : ∀ {X : ℤ}, (8 : ℤ) ∣ X → ((X : ℤ) : ZMod 8) = 0 := fun h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h
  have k := key (A : ZMod 8) (B : ZMod 8) (C : ZMod 8)
    (by have := cast0 p0; push_cast at this; linear_combination this)
    (by have := cast0 p1; push_cast at this; linear_combination this)
    (by have := cast0 p2; push_cast at this; linear_combination this)
    (by have := cast0 i0; push_cast at this; linear_combination this)
    (by have := cast0 i1; push_cast at this; linear_combination this)
    (by have := cast0 i2; push_cast at this; linear_combination this)
  have back : ∀ {X : ℤ}, ((X : ℤ) : ZMod 8) = 0 → (8 : ℤ) ∣ X := fun h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := k
  have d1 := back (X := 2 * B) (by push_cast; linear_combination k1)
  have d2 := back (X := 2 * C) (by push_cast; linear_combination k2)
  have d3 := back (X := (152) * A + (40) * B + (172) * C) (by push_cast; linear_combination k3)
  have d4 := back (X := (57) * A + (22) * B + (42) * C - A) (by push_cast; linear_combination k4)
  have d5 := back (X := (-8) * A + (60) * B + (-98) * C) (by push_cast; linear_combination k5)
  have d6 := back (X := (680) * A + (52) * B + (-1832) * C) (by push_cast; linear_combination k6)
  have d7 := back (X := (192) * A + (34) * B + (-372) * C) (by push_cast; linear_combination k7)
  have d8 := back (X := (-23) * A + (78) * B + (-158) * C - A) (by push_cast; linear_combination k8)
  set w : Torus Type321.k := (0 : ℤ) • g0 + B • g1 + C • g2 with hwdef
  have hw : InW w := ⟨by rw [hwdef, coord0']; simp, by
    rw [hwdef, gens_add, zero_gens']
    exact eq_of_dvd' (by norm_num) (by omega) (by omega)⟩
  have e0 : δ g0 = A • g0 + w := by
    rw [hδ0, hwdef]
    module
  have e1 : δ g1 = A • g1 := by
    rw [hδ1]
    conv_rhs => rw [g1_gens, smul_gens']
    exact eq_of_dvd' (by omega) (by omega) (by omega)
  have e2 : δ g2 = A • g2 := by
    rw [hδ2]
    conv_rhs => rw [g2_gens, smul_gens']
    exact eq_of_dvd' (by omega) (by omega) (by omega)
  refine ⟨A, ?_, w, hw, fun x => ?_⟩
  · obtain ⟨m, hm⟩ := p0
    exact ⟨-m, by omega⟩
  · obtain ⟨p, q, r, rfl⟩ := torus_eq_zsmul_gens _ x
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, e0, e1, e2, coord0']
    have hpar : (p : ℤ) • w = (((p : ZMod (2 ^ Type321.k 0)).val : ℕ) : ℤ) • w := by
      have hv := val_mod_two' p
      obtain ⟨j, hj⟩ : ∃ j : ℤ, (((p : ZMod (2 ^ Type321.k 0)).val : ℕ) : ℤ) = p + 2 * j := by
        refine ⟨((((p : ZMod (2 ^ Type321.k 0)).val : ℕ) : ℤ) - p) / 2, ?_⟩
        omega
      rw [hj, add_zsmul, mul_comm (2 : ℤ) j, mul_zsmul, two_zsmul, hw.2, zsmul_zero, add_zero]
    rw [← natCast_zsmul, ← hpar]
    module

private theorem inW_iff (p q r : ℤ) : InW (p • g0 + q • g1 + r • g2) ↔
    (8 : ℤ) ∣ p ∧ (8 : ℤ) ∣ 2 * q ∧ (8 : ℤ) ∣ 2 * r := by
  have h8 : ((2 ^ Type321.k 0 : ℕ) : ℤ) = 8 := by simp [Type321.k]
  constructor
  · rintro ⟨h0, h2⟩
    rw [coord0', ZMod.intCast_zmod_eq_zero_iff_dvd, h8] at h0
    rw [gens_add, zero_gens'] at h2
    obtain ⟨-, a1, a2⟩ := dvd_of_eq' h2
    exact ⟨h0, by omega, by omega⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [coord0', ZMod.intCast_zmod_eq_zero_iff_dvd, h8]
      exact h0
    · rw [gens_add, zero_gens']
      exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem even_uv (r : Torus Type321.k) (h : r + Type321.action.φuv r = 0) : (r 0).val % 2 = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ r
  rw [uv_gens, gens_add, zero_gens'] at h
  obtain ⟨h0, h1, h2⟩ := dvd_of_eq' h
  rw [coord0']
  have hv := val_mod_two' p
  omega

theorem even_t (r : Torus Type321.k) (h : r + Type321.action.φt r = 0) : (r 0).val % 2 = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ r
  rw [t_gens, gens_add, zero_gens'] at h
  obtain ⟨h0, h1, h2⟩ := dvd_of_eq' h
  rw [coord0']
  have hv := val_mod_two' p
  omega

theorem fixed (z : Torus Type321.k) (hU : Type321.action.φuv z = z) (hT : Type321.action.φt z = z) :
    InW z := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ z
  rw [uv_gens] at hU
  rw [t_gens] at hT
  obtain ⟨a0, a1, a2⟩ := dvd_of_eq' hU
  obtain ⟨b0, b1, b2⟩ := dvd_of_eq' hT
  have key : ∀ x y z : ZMod 8, x - ((-3) * x + (4) * y + (84) * z) = 0 → y - ((1) * x + (1) * y +
      (22) * z) = 0 → z - ((-1) * x + (6) * y + (-7) * z) = 0 → x - ((1) * x + (28) * z) = 0 →
      y - ((1) * x + (3) * y + (-6) * z) = 0 → z - ((2) * x + (-5) * z) = 0 →
      x = 0 ∧ 2 * y = 0 ∧ 2 * z = 0 := by
    decide
  have cast0 : ∀ {X : ℤ}, (8 : ℤ) ∣ X → ((X : ℤ) : ZMod 8) = 0 := fun h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h
  have k := key (p : ZMod 8) (q : ZMod 8) (s : ZMod 8)
    (by have := cast0 a0; push_cast at this; linear_combination this)
    (by have := cast0 a1; push_cast at this; linear_combination this)
    (by have := cast0 a2; push_cast at this; linear_combination this)
    (by have := cast0 b0; push_cast at this; linear_combination this)
    (by have := cast0 b1; push_cast at this; linear_combination this)
    (by have := cast0 b2; push_cast at this; linear_combination this)
  have back : ∀ {X : ℤ}, ((X : ℤ) : ZMod 8) = 0 → (8 : ℤ) ∣ X := fun h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp h
  rw [inW_iff]
  exact ⟨back k.1, back (X := 2 * q) (by push_cast; exact k.2.1),
    back (X := 2 * s) (by push_cast; exact k.2.2)⟩

theorem par_uv (x : Torus Type321.k) : ((Type321.action.φuv x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ x
  rw [uv_gens, coord0', coord0']
  have h1 := val_mod_two' (-3 * p + 4 * q + 84 * s)
  have h2 := val_mod_two' p
  omega

theorem par_t (x : Torus Type321.k) : ((Type321.action.φt x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ x
  rw [t_gens, coord0', coord0']
  have h1 := val_mod_two' (p + 28 * s)
  have h2 := val_mod_two' p
  omega

theorem par_u (x : Torus Type321.k) : ((Type321.action.φu x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ x
  rw [u_gens, coord0', coord0']
  have h1 := val_mod_two' (-1 * p)
  have h2 := val_mod_two' p
  omega

theorem par_ρ (x : Torus Type321.k) : ((Type321.action.φρ x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ x
  rw [rho_gens, coord0', coord0']
  have h1 := val_mod_two' (p + 4 * s)
  have h2 := val_mod_two' p
  omega

theorem W_uv (w : Torus Type321.k) (hw : InW w) : Type321.action.φuv w = w := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [uv_gens]
  exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem W_t (w : Torus Type321.k) (hw : InW w) : Type321.action.φt w = w := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [t_gens]
  exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem W_u (w : Torus Type321.k) (hw : InW w) : (Type321.action.φu w) 0 = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [u_gens]
  exact ((inW_iff _ _ _).mpr ⟨by omega, by omega, by omega⟩).1

theorem W_ρ (w : Torus Type321.k) (hw : InW w) : (Type321.action.φρ w) 0 = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [rho_gens]
  exact ((inW_iff _ _ _).mpr ⟨by omega, by omega, by omega⟩).1

theorem W_fpf (w : Torus Type321.k) (hw : InW w) (hfix : Type321.action.φρ w = w) : w = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [rho_gens] at hfix
  obtain ⟨a0, a1, a2⟩ := dvd_of_eq' hfix
  rw [zero_gens']
  exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem W_orbit (v w : Torus Type321.k) (hv : InW v) (hv0 : v ≠ 0) (hw : InW w) :
    w = 0 ∨ w = v ∨ w = Type321.action.φρ v ∨ w = v + Type321.action.φρ v := by
  refine rho_orbit v w hv.2 hv0 ?_ hw.1 hw.2
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ v
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hv
  rw [rho_gens, rho_gens, gens_add]
  exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem sq_W (v : Torus Type321.k) (hv2 : v + v = 0)
    (hρ : Type321.action.φρ (Type321.action.φρ v) = v + Type321.action.φρ v) : v 0 = 0 := by
  have h8 : ((2 ^ Type321.k 0 : ℕ) : ℤ) = 8 := by simp [Type321.k]
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ v
  rw [gens_add, zero_gens'] at hv2
  obtain ⟨a0, a1, a2⟩ := dvd_of_eq' hv2
  rw [rho_gens, rho_gens, gens_add] at hρ
  obtain ⟨b0, b1, b2⟩ := dvd_of_eq' hρ
  rw [coord0', ZMod.intCast_zmod_eq_zero_iff_dvd, h8]
  omega

theorem vFacts : VFacts StrothTypeIndex.t321 where
  two_le := by decide
  classify := classify
  even_uv := even_uv
  even_t := even_t
  fixed := fixed
  par_uv := par_uv
  par_t := par_t
  par_u := par_u
  par_ρ := par_ρ
  W_uv := W_uv
  W_t := W_t
  W_u := W_u
  W_ρ := W_ρ
  W_fpf := W_fpf
  sq_W := sq_W
  W_orbit := W_orbit

end Type321
namespace Type331

local notation "g0" => gen Type331.k 0
local notation "g1" => gen Type331.k 1
local notation "g2" => gen Type331.k 2

private theorem two_pow_k' (i : Fin 3) : (2 : ℤ) ^ Type331.k i = 8 := by
  fin_cases i <;> simp [Type331.k]

private theorem dvd_of_eq' {p q r p' q' r' : ℤ}
    (h : p • g0 + q • g1 + r • g2 = p' • g0 + q' • g1 + r' • g2) :
    (8 : ℤ) ∣ p' - p ∧ (8 : ℤ) ∣ q' - q ∧ (8 : ℤ) ∣ r' - r := by
  have := zsmul_gens_dvd_of_eq h
  simpa only [two_pow_k'] using this

private theorem eq_of_dvd' {p q r p' q' r' : ℤ} (h0 : (8 : ℤ) ∣ p' - p) (h1 : (8 : ℤ) ∣ q' - q)
    (h2 : (8 : ℤ) ∣ r' - r) : p • g0 + q • g1 + r • g2 = p' • g0 + q' • g1 + r' • g2 :=
  zsmul_gens_eq_of_dvd (by rw [two_pow_k']; exact h0) (by rw [two_pow_k']; exact h1)
    (by rw [two_pow_k']; exact h2)

private theorem smul_gens' (n a b c : ℤ) :
    n • (a • g0 + b • g1 + c • g2) = (n * a) • g0 + (n * b) • g1 + (n * c) • g2 := by
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]

private theorem zero_gens' : (0 : Torus Type331.k) = (0 : ℤ) • g0 + (0 : ℤ) • g1 + (0 : ℤ) • g2 :=
    by
  simp

private theorem g0_gens : g0 = (1 : ℤ) • g0 + (0 : ℤ) • g1 + (0 : ℤ) • g2 := by simp

private theorem g1_gens : g1 = (0 : ℤ) • g0 + (1 : ℤ) • g1 + (0 : ℤ) • g2 := by simp

private theorem g2_gens : g2 = (0 : ℤ) • g0 + (0 : ℤ) • g1 + (1 : ℤ) • g2 := by simp

private theorem val_mod_two' (X : ℤ) :
    (((X : ZMod (2 ^ Type331.k 0)).val % 2 : ℕ) : ℤ) = X % 2 := by
  have h8 : (2 ^ Type331.k 0 : ℕ) = 8 := by simp [Type331.k]
  rw [Int.natCast_mod, ZMod.val_intCast, h8]
  push_cast
  exact Int.emod_emod_of_dvd X (by norm_num)

private theorem coord0' (p q r : ℤ) : (p • g0 + q • g1 + r • g2) 0 =
    ((p : ℤ) : ZMod (2 ^ Type331.k 0)) :=
  zsmul_gens_apply_zero p q r

theorem u_gens (x y z : ℤ) : Type331.action.φu (x • g0 + y • g1 + z • g2) =
    (3 * x) • g0 + z • g1 + y • g2 := by
  rw [show Type331.action.φu = matAct Type331.k Type331.uM Type331.compat_u from rfl,
      matAct_zsmul_gens]
  have huM : ∀ i j, Type331.uM i j = (!![3, 0, 0; 0, 0, 1; 0, 1, 0] : IntMat) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Type331.uM, uMat, ofCols_apply]
  simp only [huM]
  simp [Matrix.of_apply] <;> ring_nf

private theorem g1_cyc : g1 = (3 : ℤ) • Type331.action.φuv g0 + (0 : ℤ) • Type331.action.φt g0 +
    (1 : ℤ) • Type331.action.φuv (Type331.action.φt g0) := by
  conv_rhs => rw [g0_gens, uv_gens, t_gens, uv_gens, smul_gens', smul_gens', smul_gens',
    gens_add, gens_add]
  conv_lhs => rw [g1_gens]
  exact eq_of_dvd' (by norm_num) (by norm_num) (by norm_num)

private theorem g2_cyc : g2 = (1 : ℤ) • Type331.action.φuv g0 + (3 : ℤ) • Type331.action.φt g0 +
    (0 : ℤ) • Type331.action.φuv (Type331.action.φt g0) := by
  conv_rhs => rw [g0_gens, uv_gens, t_gens, uv_gens, smul_gens', smul_gens', smul_gens',
    gens_add, gens_add]
  conv_lhs => rw [g2_gens]
  exact eq_of_dvd' (by norm_num) (by norm_num) (by norm_num)

theorem classify (δ : Torus Type331.k →+ Torus Type331.k)
    (hU : ∀ x, δ (Type331.action.φuv x) = Type331.action.φuv (δ x))
    (hT : ∀ x, δ (Type331.action.φt x) = Type331.action.φt (δ x))
    (h2 : ∀ x, x + x = 0 → δ x = x) (hinv : ∀ x, δ (δ x) = x) :
    ∃ α : ℤ, Odd α ∧ ∃ w, InW w ∧ ∀ x, δ x = α • x + (x 0).val • w := by
  obtain ⟨A, B, C, hδ0⟩ := torus_eq_zsmul_gens _ (δ g0)
  have hcyc : ∀ (p q r : ℤ), δ (p • Type331.action.φuv g0 + q • Type331.action.φt g0 +
      r • Type331.action.φuv (Type331.action.φt g0)) =
      p • Type331.action.φuv (δ g0) + q • Type331.action.φt (δ g0) +
        r • Type331.action.φuv (Type331.action.φt (δ g0)) := fun p q r => by
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hU, hT, hU, hT]
  have hδ1 : δ g1 = ((-48) * A + (24) * B + (-148) * C) • g0 + ((-55) * A + (6) * B +
      (58) * C) • g1 + ((-16) * A + (36) * B + (-82) * C) • g2 := by
    conv_lhs => rw [g1_cyc, hcyc, hδ0, uv_gens, t_gens, uv_gens, smul_gens', smul_gens',
      smul_gens', gens_add, gens_add]
    exact eq_of_dvd' ⟨0, by ring⟩ ⟨0, by ring⟩ ⟨0, by ring⟩
  have hδ2 : δ g2 = ((4) * B + (104) * C) • g0 + ((8) * A + (10) * B + (20) * C) • g1 +
      ((-7) * A + (6) * B + (-6) * C) • g2 := by
    conv_lhs => rw [g2_cyc, hcyc, hδ0, uv_gens, t_gens, uv_gens, smul_gens', smul_gens',
      smul_gens', gens_add, gens_add]
    exact eq_of_dvd' ⟨0, by ring⟩ ⟨0, by ring⟩ ⟨0, by ring⟩
  have hi := hinv g0
  rw [hδ0, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hδ0, hδ1, hδ2, smul_gens',
    smul_gens', smul_gens', gens_add, gens_add] at hi
  conv at hi => rhs; rw [g0_gens]
  obtain ⟨i0, i1, i2⟩ := dvd_of_eq' hi
  have h4 := h2 ((4 : ℤ) • g0) (by
    rw [g0_gens, smul_gens', gens_add, zero_gens']
    exact eq_of_dvd' (by norm_num) (by norm_num) (by norm_num))
  rw [map_zsmul, hδ0, smul_gens'] at h4
  conv at h4 => rhs; rw [g0_gens, smul_gens']
  obtain ⟨p0, p1, p2⟩ := dvd_of_eq' h4
  have key : ∀ a b c : ZMod 8, 4 * 1 - 4 * a = 0 → 4 * 0 - 4 * b = 0 → 4 * 0 - 4 * c = 0 →
      1 - (a * a + b * ((-48) * a + (24) * b + (-148) * c) + c * ((4) * b + (104) * c)) = 0 →
          0 - (a * b + b * ((-55) * a + (6) * b + (58) * c) + c * ((8) * a + (10) * b +
          (20) * c)) = 0 → 0 - (a * c + b * ((-16) * a + (36) * b + (-82) * c) + c * ((-7) * a +
          (6) * b + (-6) * c)) = 0 →
      2 * b = 0 ∧ 2 * c = 0 ∧ (-48) * a + (24) * b + (-148) * c = 0 ∧ (-55) * a + (6) * b +
          (58) * c - a = 0 ∧ (-16) * a + (36) * b + (-82) * c = 0 ∧
        (4) * b + (104) * c = 0 ∧ (8) * a + (10) * b + (20) * c = 0 ∧ (-7) * a + (6) * b +
            (-6) * c - a = 0 := by
    decide
  have cast0 : ∀ {X : ℤ}, (8 : ℤ) ∣ X → ((X : ℤ) : ZMod 8) = 0 := fun h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h
  have k := key (A : ZMod 8) (B : ZMod 8) (C : ZMod 8)
    (by have := cast0 p0; push_cast at this; linear_combination this)
    (by have := cast0 p1; push_cast at this; linear_combination this)
    (by have := cast0 p2; push_cast at this; linear_combination this)
    (by have := cast0 i0; push_cast at this; linear_combination this)
    (by have := cast0 i1; push_cast at this; linear_combination this)
    (by have := cast0 i2; push_cast at this; linear_combination this)
  have back : ∀ {X : ℤ}, ((X : ℤ) : ZMod 8) = 0 → (8 : ℤ) ∣ X := fun h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := k
  have d1 := back (X := 2 * B) (by push_cast; linear_combination k1)
  have d2 := back (X := 2 * C) (by push_cast; linear_combination k2)
  have d3 := back (X := (-48) * A + (24) * B + (-148) * C) (by push_cast; linear_combination k3)
  have d4 := back (X := (-55) * A + (6) * B + (58) * C - A) (by push_cast; linear_combination k4)
  have d5 := back (X := (-16) * A + (36) * B + (-82) * C) (by push_cast; linear_combination k5)
  have d6 := back (X := (4) * B + (104) * C) (by push_cast; linear_combination k6)
  have d7 := back (X := (8) * A + (10) * B + (20) * C) (by push_cast; linear_combination k7)
  have d8 := back (X := (-7) * A + (6) * B + (-6) * C - A) (by push_cast; linear_combination k8)
  set w : Torus Type331.k := (0 : ℤ) • g0 + B • g1 + C • g2 with hwdef
  have hw : InW w := ⟨by rw [hwdef, coord0']; simp, by
    rw [hwdef, gens_add, zero_gens']
    exact eq_of_dvd' (by norm_num) (by omega) (by omega)⟩
  have e0 : δ g0 = A • g0 + w := by
    rw [hδ0, hwdef]
    module
  have e1 : δ g1 = A • g1 := by
    rw [hδ1]
    conv_rhs => rw [g1_gens, smul_gens']
    exact eq_of_dvd' (by omega) (by omega) (by omega)
  have e2 : δ g2 = A • g2 := by
    rw [hδ2]
    conv_rhs => rw [g2_gens, smul_gens']
    exact eq_of_dvd' (by omega) (by omega) (by omega)
  refine ⟨A, ?_, w, hw, fun x => ?_⟩
  · obtain ⟨m, hm⟩ := p0
    exact ⟨-m, by omega⟩
  · obtain ⟨p, q, r, rfl⟩ := torus_eq_zsmul_gens _ x
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, e0, e1, e2, coord0']
    have hpar : (p : ℤ) • w = (((p : ZMod (2 ^ Type331.k 0)).val : ℕ) : ℤ) • w := by
      have hv := val_mod_two' p
      obtain ⟨j, hj⟩ : ∃ j : ℤ, (((p : ZMod (2 ^ Type331.k 0)).val : ℕ) : ℤ) = p + 2 * j := by
        refine ⟨((((p : ZMod (2 ^ Type331.k 0)).val : ℕ) : ℤ) - p) / 2, ?_⟩
        omega
      rw [hj, add_zsmul, mul_comm (2 : ℤ) j, mul_zsmul, two_zsmul, hw.2, zsmul_zero, add_zero]
    rw [← natCast_zsmul, ← hpar]
    module

private theorem inW_iff (p q r : ℤ) : InW (p • g0 + q • g1 + r • g2) ↔
    (8 : ℤ) ∣ p ∧ (8 : ℤ) ∣ 2 * q ∧ (8 : ℤ) ∣ 2 * r := by
  have h8 : ((2 ^ Type331.k 0 : ℕ) : ℤ) = 8 := by simp [Type331.k]
  constructor
  · rintro ⟨h0, h2⟩
    rw [coord0', ZMod.intCast_zmod_eq_zero_iff_dvd, h8] at h0
    rw [gens_add, zero_gens'] at h2
    obtain ⟨-, a1, a2⟩ := dvd_of_eq' h2
    exact ⟨h0, by omega, by omega⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [coord0', ZMod.intCast_zmod_eq_zero_iff_dvd, h8]
      exact h0
    · rw [gens_add, zero_gens']
      exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem even_uv (r : Torus Type331.k) (h : r + Type331.action.φuv r = 0) : (r 0).val % 2 = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ r
  rw [uv_gens, gens_add, zero_gens'] at h
  obtain ⟨h0, h1, h2⟩ := dvd_of_eq' h
  rw [coord0']
  have hv := val_mod_two' p
  omega

theorem even_t (r : Torus Type331.k) (h : r + Type331.action.φt r = 0) : (r 0).val % 2 = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ r
  rw [t_gens, gens_add, zero_gens'] at h
  obtain ⟨h0, h1, h2⟩ := dvd_of_eq' h
  rw [coord0']
  have hv := val_mod_two' p
  omega

theorem fixed (z : Torus Type331.k) (hU : Type331.action.φuv z = z) (hT : Type331.action.φt z = z) :
    InW z := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ z
  rw [uv_gens] at hU
  rw [t_gens] at hT
  obtain ⟨a0, a1, a2⟩ := dvd_of_eq' hU
  obtain ⟨b0, b1, b2⟩ := dvd_of_eq' hT
  have key : ∀ x y z : ZMod 8, x - ((-3) * x + (4) * y + (20) * z) = 0 → y - ((5) * x + (1) * y +
      (38) * z) = 0 → z - ((-1) * x + (6) * y + (9) * z) = 0 → x - ((1) * x + (28) * z) = 0 →
      y - ((1) * x + (3) * y + (-6) * z) = 0 → z - ((-2) * x + (-5) * z) = 0 →
      x = 0 ∧ 2 * y = 0 ∧ 2 * z = 0 := by
    decide
  have cast0 : ∀ {X : ℤ}, (8 : ℤ) ∣ X → ((X : ℤ) : ZMod 8) = 0 := fun h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h
  have k := key (p : ZMod 8) (q : ZMod 8) (s : ZMod 8)
    (by have := cast0 a0; push_cast at this; linear_combination this)
    (by have := cast0 a1; push_cast at this; linear_combination this)
    (by have := cast0 a2; push_cast at this; linear_combination this)
    (by have := cast0 b0; push_cast at this; linear_combination this)
    (by have := cast0 b1; push_cast at this; linear_combination this)
    (by have := cast0 b2; push_cast at this; linear_combination this)
  have back : ∀ {X : ℤ}, ((X : ℤ) : ZMod 8) = 0 → (8 : ℤ) ∣ X := fun h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp h
  rw [inW_iff]
  exact ⟨back k.1, back (X := 2 * q) (by push_cast; exact k.2.1),
    back (X := 2 * s) (by push_cast; exact k.2.2)⟩

theorem par_uv (x : Torus Type331.k) : ((Type331.action.φuv x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ x
  rw [uv_gens, coord0', coord0']
  have h1 := val_mod_two' (-3 * p + 4 * q + 20 * s)
  have h2 := val_mod_two' p
  omega

theorem par_t (x : Torus Type331.k) : ((Type331.action.φt x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ x
  rw [t_gens, coord0', coord0']
  have h1 := val_mod_two' (p + 28 * s)
  have h2 := val_mod_two' p
  omega

theorem par_u (x : Torus Type331.k) : ((Type331.action.φu x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ x
  rw [u_gens, coord0', coord0']
  have h1 := val_mod_two' (3 * p)
  have h2 := val_mod_two' p
  omega

theorem par_ρ (x : Torus Type331.k) : ((Type331.action.φρ x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ x
  rw [rho_gens, coord0', coord0']
  have h1 := val_mod_two' (p + 4 * s)
  have h2 := val_mod_two' p
  omega

theorem W_uv (w : Torus Type331.k) (hw : InW w) : Type331.action.φuv w = w := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [uv_gens]
  exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem W_t (w : Torus Type331.k) (hw : InW w) : Type331.action.φt w = w := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [t_gens]
  exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem W_u (w : Torus Type331.k) (hw : InW w) : (Type331.action.φu w) 0 = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [u_gens]
  exact ((inW_iff _ _ _).mpr ⟨by omega, by omega, by omega⟩).1

theorem W_ρ (w : Torus Type331.k) (hw : InW w) : (Type331.action.φρ w) 0 = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [rho_gens]
  exact ((inW_iff _ _ _).mpr ⟨by omega, by omega, by omega⟩).1

theorem W_fpf (w : Torus Type331.k) (hw : InW w) (hfix : Type331.action.φρ w = w) : w = 0 := by
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hw
  rw [rho_gens] at hfix
  obtain ⟨a0, a1, a2⟩ := dvd_of_eq' hfix
  rw [zero_gens']
  exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem W_orbit (v w : Torus Type331.k) (hv : InW v) (hv0 : v ≠ 0) (hw : InW w) :
    w = 0 ∨ w = v ∨ w = Type331.action.φρ v ∨ w = v + Type331.action.φρ v := by
  refine rho_orbit v w hv.2 hv0 ?_ hw.1 hw.2
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ v
  obtain ⟨h0, h1, h2⟩ := (inW_iff p q s).mp hv
  rw [rho_gens, rho_gens, gens_add]
  exact eq_of_dvd' (by omega) (by omega) (by omega)

theorem sq_W (v : Torus Type331.k) (hv2 : v + v = 0)
    (hρ : Type331.action.φρ (Type331.action.φρ v) = v + Type331.action.φρ v) : v 0 = 0 := by
  have h8 : ((2 ^ Type331.k 0 : ℕ) : ℤ) = 8 := by simp [Type331.k]
  obtain ⟨p, q, s, rfl⟩ := torus_eq_zsmul_gens _ v
  rw [gens_add, zero_gens'] at hv2
  obtain ⟨a0, a1, a2⟩ := dvd_of_eq' hv2
  rw [rho_gens, rho_gens, gens_add] at hρ
  obtain ⟨b0, b1, b2⟩ := dvd_of_eq' hρ
  rw [coord0', ZMod.intCast_zmod_eq_zero_iff_dvd, h8]
  omega

theorem vFacts : VFacts StrothTypeIndex.t331 where
  two_le := by decide
  classify := classify
  even_uv := even_uv
  even_t := even_t
  fixed := fixed
  par_uv := par_uv
  par_t := par_t
  par_u := par_u
  par_ρ := par_ρ
  W_uv := W_uv
  W_t := W_t
  W_u := W_u
  W_ρ := W_ρ
  W_fpf := W_fpf
  sq_W := sq_W
  W_orbit := W_orbit

end Type331
end CFSG.CGT.Stroth77
