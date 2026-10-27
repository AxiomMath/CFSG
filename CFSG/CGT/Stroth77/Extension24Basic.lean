module

public import CFSG.CGT.Stroth77.Extension22FourProof

public section

namespace CFSG.CGT.Stroth77

theorem m_t300 (n : ℕ) : (StrothTypeIndex.t300 n).m = n := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t300 n)) 0
  simp only [Matrix.cons_val_zero] at h
  have hk : (StrothTypeIndex.t300 n).k 0 = n := rfl
  rw [hk] at h
  exact h.symm

theorem n_t300 (n : ℕ) : (StrothTypeIndex.t300 n).n = n := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t300 n)) 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
  have hk : (StrothTypeIndex.t300 n).k 1 = n := rfl
  rw [hk] at h
  exact h.symm

theorem zsmul_gens_apply_zero {k : Fin 3 → ℕ} (p q r : ℤ) :
    (p • gen k 0 + q • gen k 1 + r • gen k 2) 0 = (p : ZMod (2 ^ k 0)) := by
  simp [gen, Pi.single_apply, zsmul_eq_mul]

theorem zsmul_gens_apply_one {k : Fin 3 → ℕ} (p q r : ℤ) :
    (p • gen k 0 + q • gen k 1 + r • gen k 2) 1 = (q : ZMod (2 ^ k 1)) := by
  simp [gen, Pi.single_apply, zsmul_eq_mul]

theorem zsmul_gens_apply_two {k : Fin 3 → ℕ} (p q r : ℤ) :
    (p • gen k 0 + q • gen k 1 + r • gen k 2) 2 = (r : ZMod (2 ^ k 2)) := by
  simp [gen, Pi.single_apply, zsmul_eq_mul]

theorem nsmul_zsmul_gens {k : Fin 3 → ℕ} (M : ℕ) (p q r : ℤ) :
    M • (p • gen k 0 + q • gen k 1 + r • gen k 2) =
      ((M : ℤ) * p) • gen k 0 + ((M : ℤ) * q) • gen k 1 + ((M : ℤ) * r) • gen k 2 := by
  rw [smul_add, smul_add, ← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul,
    smul_smul, smul_smul, smul_smul]

theorem zsmul_gens_dvd_of_eq {k : Fin 3 → ℕ} {p q r p' q' r' : ℤ}
    (h : p • gen k 0 + q • gen k 1 + r • gen k 2 = p' • gen k 0 + q' • gen k 1 + r' • gen k 2) :
    (2 : ℤ) ^ k 0 ∣ p' - p ∧ (2 : ℤ) ^ k 1 ∣ q' - q ∧ (2 : ℤ) ^ k 2 ∣ r' - r := by
  refine ⟨?_, ?_, ?_⟩
  · have h0 := congrFun h 0
    rw [zsmul_gens_apply_zero, zsmul_gens_apply_zero] at h0
    exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub p p' (2 ^ k 0)).mp h0
  · have h1 := congrFun h 1
    rw [zsmul_gens_apply_one, zsmul_gens_apply_one] at h1
    exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub q q' (2 ^ k 1)).mp h1
  · have h2 := congrFun h 2
    rw [zsmul_gens_apply_two, zsmul_gens_apply_two] at h2
    exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub r r' (2 ^ k 2)).mp h2

theorem zsmul_gens_eq_of_dvd {k : Fin 3 → ℕ} {p q r p' q' r' : ℤ}
    (h0 : (2 : ℤ) ^ k 0 ∣ p' - p) (h1 : (2 : ℤ) ^ k 1 ∣ q' - q)
    (h2 : (2 : ℤ) ^ k 2 ∣ r' - r) :
    p • gen k 0 + q • gen k 1 + r • gen k 2 = p' • gen k 0 + q' • gen k 1 + r' • gen k 2 := by
  have e0 : (p : ZMod (2 ^ k 0)) = p' :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub p p' (2 ^ k 0)).mpr (by exact_mod_cast h0)
  have e1 : (q : ZMod (2 ^ k 1)) = q' :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub q q' (2 ^ k 1)).mpr (by exact_mod_cast h1)
  have e2 : (r : ZMod (2 ^ k 2)) = r' :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub r r' (2 ^ k 2)).mpr (by exact_mod_cast h2)
  funext i
  fin_cases i
  · exact (zsmul_gens_apply_zero p q r).trans (e0.trans (zsmul_gens_apply_zero p' q' r').symm)
  · exact (zsmul_gens_apply_one p q r).trans (e1.trans (zsmul_gens_apply_one p' q' r').symm)
  · exact (zsmul_gens_apply_two p q r).trans (e2.trans (zsmul_gens_apply_two p' q' r').symm)

theorem type300_rho_apply_gens (n : ℕ) (i j l : ℤ) :
    (Type300.action n).φρ (i • gen (Type300.k n) 0 + j • gen (Type300.k n) 1 +
        l • gen (Type300.k n) 2) =
      (i - 4 * l) • gen (Type300.k n) 0 + (-l) • gen (Type300.k n) 1 +
        (j - l) • gen (Type300.k n) 2 := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
  have hc := Type300.rho_c n
  have ha := Type300.rho_a n
  have hb := Type300.rho_b n
  simp only [Torus.c, Torus.a, Torus.b] at hc ha hb
  rw [hc, ha, hb]
  module

theorem type300_t_apply_gens (n : ℕ) (i j l : ℤ) :
    (Type300.action n).φt (i • gen (Type300.k n) 0 + j • gen (Type300.k n) 1 +
        l • gen (Type300.k n) 2) =
      (i - 4 * l) • gen (Type300.k n) 0 + (i - j - 2 * l) • gen (Type300.k n) 1 +
        (-l) • gen (Type300.k n) 2 := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
  have hc := Type300.t_c n
  have ha := Type300.t_a n
  have hb := Type300.t_b n
  simp only [Torus.c, Torus.a, Torus.b] at hc ha hb
  rw [hc, ha, hb]
  module

theorem t300_fixed_rho_t_mod (n M : ℕ) (y : Torus (Type300.k n))
    (hρ : ∃ z : Torus (Type300.k n), M • z = (Type300.action n).φρ y - y)
    (ht : ∃ z : Torus (Type300.k n), M • z = (Type300.action n).φt y - y) :
    ∃ z : Torus (Type300.k n), M • z = y := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type300.k n) y
  obtain ⟨zρ, hzρ⟩ := hρ
  obtain ⟨zt, hzt⟩ := ht
  obtain ⟨a0, a1, a2, rfl⟩ := torus_eq_zsmul_gens (Type300.k n) zρ
  obtain ⟨b0, b1, b2, rfl⟩ := torus_eq_zsmul_gens (Type300.k n) zt
  rw [type300_rho_apply_gens, nsmul_zsmul_gens] at hzρ
  rw [type300_t_apply_gens, nsmul_zsmul_gens] at hzt
  have eρ : (i - 4 * l) • gen (Type300.k n) 0 + (-l) • gen (Type300.k n) 1 +
        (j - l) • gen (Type300.k n) 2 -
      (i • gen (Type300.k n) 0 + j • gen (Type300.k n) 1 + l • gen (Type300.k n) 2) =
      (-4 * l) • gen (Type300.k n) 0 + (-l - j) • gen (Type300.k n) 1 +
        (j - 2 * l) • gen (Type300.k n) 2 := by
    module
  have et : (i - 4 * l) • gen (Type300.k n) 0 + (i - j - 2 * l) • gen (Type300.k n) 1 +
        (-l) • gen (Type300.k n) 2 -
      (i • gen (Type300.k n) 0 + j • gen (Type300.k n) 1 + l • gen (Type300.k n) 2) =
      (-4 * l) • gen (Type300.k n) 0 + (i - 2 * j - 2 * l) • gen (Type300.k n) 1 +
        (-2 * l) • gen (Type300.k n) 2 := by
    module
  rw [eρ] at hzρ
  rw [et] at hzt
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hzρ
  obtain ⟨-, ht1, ht2⟩ := zsmul_gens_dvd_of_eq hzt
  change (2 : ℤ) ^ n ∣ _ at hρ1 hρ2 ht1 ht2
  refine ⟨(b1 + 2 * (-a1 - (-(a1 + a2) + b2)) + 2 * (-(a1 + a2) + b2)) • gen (Type300.k n) 0 +
    (-a1 - (-(a1 + a2) + b2)) • gen (Type300.k n) 1 +
    (-(a1 + a2) + b2) • gen (Type300.k n) 2, ?_⟩
  rw [nsmul_zsmul_gens]
  apply zsmul_gens_eq_of_dvd
  · change (2 : ℤ) ^ n ∣ _
    have h := dvd_sub ht1 (dvd_mul_of_dvd_right hρ1 2)
    convert h using 1
    ring
  · change (2 : ℤ) ^ n ∣ _
    have h := dvd_sub hρ2 ht2
    convert h using 1
    ring
  · change (2 : ℤ) ^ n ∣ _
    have h := dvd_sub ht2 (dvd_add hρ1 hρ2)
    convert h using 1
    ring

theorem t300_fixed_rho_t (n : ℕ) (y : Torus (Type300.k n))
    (hρ : (Type300.action n).φρ y = y) (ht : (Type300.action n).φt y = y) : y = 0 := by
  obtain ⟨z, hz⟩ := t300_fixed_rho_t_mod n 0 y ⟨0, by rw [hρ, sub_self, zero_smul]⟩
    ⟨0, by rw [ht, sub_self, zero_smul]⟩
  rw [← hz, zero_smul]

section Group

variable {S : Type*} [Group S] [Finite S] {B : Subgroup S} {n : ℕ}

theorem ec_conjBy_ρ_mul_inv300 (D : StrothTypeData B (StrothTypeIndex.t300 n)) (y : B) :
    D.ec (conjBy D.ρ_mem y * y⁻¹) = (StrothTypeIndex.t300 n).action.φρ (D.ec y) - D.ec y := by
  rw [D.ec_mul, D.ec_inv, sub_eq_add_neg]
  congr 1
  exact D.ρ_conj y

theorem ec_conjBy_t_mul_inv300 (D : StrothTypeData B (StrothTypeIndex.t300 n)) (y : B) :
    D.ec (conjBy D.t_mem y * y⁻¹) = (StrothTypeIndex.t300 n).action.φt (D.ec y) - D.ec y := by
  rw [D.ec_mul, D.ec_inv, sub_eq_add_neg]
  congr 1
  exact D.t_conj y

theorem t300_fixed_rho_t_of_mem (D : StrothTypeData B (StrothTypeIndex.t300 n)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t300 n).action.φρ (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t300 n).action.φρ (D.ec y) from
      D.ρ_conj y, hρ]
  have ht' : (StrothTypeIndex.t300 n).action.φt (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t300 n).action.φt (D.ec y) from
      D.t_conj y, ht]
  exact D.ec_eq_zero_iff.mp (t300_fixed_rho_t n (D.ec y) hρ' ht')

theorem t300_fixed_rho_t_mod_four_of_mem (D : StrothTypeData B (StrothTypeIndex.t300 n))
    {y : B} (hρ : conjBy D.ρ_mem y * y⁻¹ ∈ fourB D) (ht : conjBy D.t_mem y * y⁻¹ ∈ fourB D) :
    y ∈ fourB D := by
  rw [mem_fourB_iff] at hρ ht ⊢
  rw [ec_conjBy_ρ_mul_inv300] at hρ
  rw [ec_conjBy_t_mul_inv300] at ht
  exact t300_fixed_rho_t_mod n 4 (D.ec y) hρ ht

theorem t300_fixed_rho_t_mod_two_of_mem (D : StrothTypeData B (StrothTypeIndex.t300 n))
    {y : B} (hρ : ∃ z : Torus (StrothTypeIndex.t300 n).k, 2 • z = D.ec (conjBy D.ρ_mem y * y⁻¹))
    (ht : ∃ z : Torus (StrothTypeIndex.t300 n).k, 2 • z = D.ec (conjBy D.t_mem y * y⁻¹)) :
    ∃ z : Torus (StrothTypeIndex.t300 n).k, 2 • z = D.ec y := by
  rw [ec_conjBy_ρ_mul_inv300] at hρ
  rw [ec_conjBy_t_mul_inv300] at ht
  exact t300_fixed_rho_t_mod n 2 (D.ec y) hρ ht

end Group

end CFSG.CGT.Stroth77
