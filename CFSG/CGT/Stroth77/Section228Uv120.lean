module

public import CFSG.CGT.Stroth77.Section228Uv

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G}

theorem t120_iV_odd (m : ℕ) : Odd (Type120.iV (m + 1)) := by
  have h3 := Type120.three_mul_iV (m + 1)
  have he : Even ((2 : ℤ) ^ (2 * (m + 1) + 1)) :=
    Even.pow_of_ne_zero (by norm_num : Even (2 : ℤ)) (by omega)
  obtain ⟨k, hk⟩ := he.add_one
  exact ⟨k - Type120.iV (m + 1), by omega⟩

theorem t120_FV_odd (m : ℕ) : Odd (Type120.FV (m + 1)) := by
  have h3 := Type120.three_mul_FV (m + 1)
  have he : Even ((4 : ℤ) ^ (m + 1)) :=
    Even.pow_of_ne_zero (by norm_num : Even (4 : ℤ)) (by omega)
  obtain ⟨k, hk⟩ := he.sub_odd odd_one
  exact ⟨k - Type120.FV (m + 1), by omega⟩

theorem t120_iV_modEq_eight (m : ℕ) : Type120.iV (m + 1) ≡ 3 [ZMOD 8] := by
  obtain ⟨K, hK⟩ : ∃ K : ℤ, (2 : ℤ) ^ (2 * (m + 1) + 1) = 8 * K := by
    refine ⟨(2 : ℤ) ^ (2 * (m + 1) + 1 - 3), ?_⟩
    rw [show 2 * (m + 1) + 1 = 3 + (2 * (m + 1) + 1 - 3) by omega, pow_add]
    norm_num
  have h3 := Type120.three_mul_iV (m + 1)
  rw [Int.modEq_iff_dvd]
  refine ⟨Type120.iV (m + 1) - 3 * K, by omega⟩

theorem two_pow_mul_of_odd_modEq {m : ℕ} {z : ℤ} (hz : Odd z) :
    (2 : ℤ) ^ m * z ≡ (2 : ℤ) ^ m [ZMOD 2 ^ (m + 1)] := by
  obtain ⟨a, rfl⟩ := hz
  rw [Int.modEq_iff_dvd]
  refine ⟨-a, by ring⟩

theorem two_pow_mul_of_even_modEq {m : ℕ} {z : ℤ} (hz : Even z) :
    (2 : ℤ) ^ m * z ≡ 0 [ZMOD 2 ^ (m + 1)] := by
  obtain ⟨a, rfl⟩ := hz
  rw [Int.modEq_iff_dvd]
  refine ⟨-a, by ring⟩

theorem t120_u_a_half (m : ℕ) (hm : 3 ≤ m) :
    (StrothTypeIndex.t120 m hm).action.φu
        ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k)) =
      (2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k) := by
  let hd : Type120.Data m (Type120.iV (m + 1)) (Type120.FV (m + 1))
      (Type120.GV (m + 1)) := Type120.data m (by omega)
  have hva : (2 ^ m : ℕ) • Torus.a (k := Type120.k m) =
      Torus.ofInt (Type120.k m) ![0, (2 : ℤ) ^ m, 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    funext j
    fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply]
  have hvb : (2 ^ m : ℕ) • Torus.b (k := Type120.k m) =
      Torus.ofInt (Type120.k m) ![0, 0, (2 : ℤ) ^ m] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    funext j
    fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply]
  change (Type120.action hd).φu ((2 ^ m : ℕ) • Torus.a (k := Type120.k m)) =
    (2 ^ m : ℕ) • Torus.b (k := Type120.k m)
  rw [hva, hvb]
  rw [show (Type120.action hd).φu =
      matAct (Type120.k m) (Type120.uM (Type120.FV (m + 1))) (Type120.compat_u hd)
    from rfl, matAct_ofInt]
  have hvec : Type120.uM (Type120.FV (m + 1)) *ᵥ ![0, (2 : ℤ) ^ m, 0] =
      ![(2 : ℤ) ^ m * (-4 * Type120.FV (m + 1)), 0, (2 : ℤ) ^ m] := by
    rw [show Type120.uM (Type120.FV (m + 1)) =
      uMat ![-1, 0, 0] (-4 * Type120.FV (m + 1)) from rfl, uMat_mulVec]
    funext j
    fin_cases j <;> simp
  rw [hvec, Torus.ofInt_eq_ofInt_iff]
  intro j
  fin_cases j
  · change (2 : ℤ) ^ m * (-4 * Type120.FV (m + 1)) ≡ 0 [ZMOD 2 ^ m]
    rw [Int.modEq_iff_dvd]
    exact ⟨4 * Type120.FV (m + 1), by ring⟩
  · exact Int.ModEq.refl _
  · change (2 : ℤ) ^ m ≡ (2 : ℤ) ^ m [ZMOD 2 ^ (m + 1)]
    exact Int.ModEq.refl _

theorem t120_uv_fixes_a_half (m : ℕ) (hm : 3 ≤ m) :
    (StrothTypeIndex.t120 m hm).action.φuv
        ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k)) =
      (2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k) := by
  let hd : Type120.Data m (Type120.iV (m + 1)) (Type120.FV (m + 1))
      (Type120.GV (m + 1)) := Type120.data m (by omega)
  have hi : Odd (Type120.iV (m + 1)) := t120_iV_odd m
  have hva : (2 ^ m : ℕ) • Torus.a (k := Type120.k m) =
      Torus.ofInt (Type120.k m) ![0, (2 : ℤ) ^ m, 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    funext j
    fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply]
  change (Type120.action hd).φuv ((2 ^ m : ℕ) • Torus.a (k := Type120.k m)) =
    (2 ^ m : ℕ) • Torus.a (k := Type120.k m)
  rw [hva]
  rw [show (Type120.action hd).φuv =
      matAct (Type120.k m)
        (Type120.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)))
        (Type120.compat_uv hd) from rfl, matAct_ofInt]
  have hvec : Type120.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1))
        (Type120.GV (m + 1)) *ᵥ ![0, (2 : ℤ) ^ m, 0] =
      ![(2 : ℤ) ^ m * (2 * Type120.FV (m + 1) * Type120.iV (m + 1)),
        (2 : ℤ) ^ m * (-5 * Type120.iV (m + 1)),
        (2 : ℤ) ^ m * (2 * Type120.iV (m + 1))] := by
    rw [show Type120.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1))
        (Type120.GV (m + 1)) =
        ofCols ![-Type120.iV (m + 1), 2, -2]
          (Type120.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)))
          (Type120.ρM *ᵥ (Type120.tM (Type120.iV (m + 1)) (Type120.FV (m + 1))
            (Type120.GV (m + 1)) *ᵥ Type120.uvA (Type120.iV (m + 1))
              (Type120.FV (m + 1)))) from rfl, ofCols_mulVec]
    funext j
    fin_cases j <;> simp [Type120.uvA]
  rw [hvec, Torus.ofInt_eq_ofInt_iff]
  intro j
  fin_cases j
  · change (2 : ℤ) ^ m * (2 * Type120.FV (m + 1) * Type120.iV (m + 1)) ≡
        0 [ZMOD 2 ^ m]
    rw [Int.modEq_iff_dvd]
    exact ⟨-2 * Type120.FV (m + 1) * Type120.iV (m + 1), by ring⟩
  · change (2 : ℤ) ^ m * (-5 * Type120.iV (m + 1)) ≡
        (2 : ℤ) ^ m [ZMOD 2 ^ (m + 1)]
    exact two_pow_mul_of_odd_modEq (m := m)
      ((by norm_num : Odd (-5 : ℤ)).mul hi)
  · change (2 : ℤ) ^ m * (2 * Type120.iV (m + 1)) ≡ 0 [ZMOD 2 ^ (m + 1)]
    exact two_pow_mul_of_even_modEq (m := m) (even_two.mul_right _)

theorem t120_uv_fixes_b_half (m : ℕ) (hm : 3 ≤ m) :
    (StrothTypeIndex.t120 m hm).action.φuv
        ((2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k)) =
      (2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k) := by
  have hcomm : ∀ v : Torus (StrothTypeIndex.t120 m hm).k,
      (StrothTypeIndex.t120 m hm).action.φu
          ((StrothTypeIndex.t120 m hm).action.φuv v) =
        (StrothTypeIndex.t120 m hm).action.φuv
          ((StrothTypeIndex.t120 m hm).action.φu v) :=
    fun v => DFunLike.congr_fun (StrothTypeIndex.t120 m hm).action.rels.uv_comm_u v
  calc (StrothTypeIndex.t120 m hm).action.φuv
        ((2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k))
      = (StrothTypeIndex.t120 m hm).action.φuv
          ((StrothTypeIndex.t120 m hm).action.φu
            ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k))) := by
          rw [t120_u_a_half m hm]
    _ = (StrothTypeIndex.t120 m hm).action.φu
          ((StrothTypeIndex.t120 m hm).action.φuv
            ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k))) :=
          (hcomm _).symm
    _ = (StrothTypeIndex.t120 m hm).action.φu
          ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k)) := by
          rw [t120_uv_fixes_a_half m hm]
    _ = (2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k) :=
          t120_u_a_half m hm

theorem t120_φuv_a_add_b {m : ℕ} {i F G : ℤ} (hd : Type120.Data m i F G) :
    (Type120.action hd).φuv
        (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m)) =
      Torus.ofInt (Type120.k m) ![
        2 * F * i + (2 * F * i ^ 2 - 8 * F * i - 20 * G * i ^ 2 - 60 * i ^ 2),
        -5 * i + (-8 * F * i - 26 * i ^ 2),
        2 * i + (-4 * F * i + 5 * i ^ 2)] := by
  rw [map_add, Type120.uv_a hd, Type120.uv_b hd]
  funext j
  fin_cases j <;>
    simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply, Torus.ofInt, zsmul_eq_mul]
  all_goals ring

theorem t120_preimage_coord_zero {m : ℕ} (hm : 3 ≤ m) (t b G : ℤ) :
    (2 : ℤ) ^ m ∣ 0 - (3 * 2 ^ (m - 2)) *
      (2 * (2 * b + 1) * (8 * t + 3) +
        (2 * (2 * b + 1) * (8 * t + 3) ^ 2 - 8 * (2 * b + 1) * (8 * t + 3) -
          20 * G * (8 * t + 3) ^ 2 - 60 * (8 * t + 3) ^ 2)) := by
  have hpow4 : (2 : ℤ) ^ (m - 2) * 4 = 2 ^ m := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add, show m - 2 + 2 = m by omega]
  refine ⟨-(192 * t ^ 2 * b - 960 * t ^ 2 * G - 2784 * t ^ 2 + 72 * t * b - 720 * t * G -
    2124 * t - 135 * G - 405), ?_⟩
  have hc0 : 3 * (2 * (2 * b + 1) * (8 * t + 3) +
      (2 * (2 * b + 1) * (8 * t + 3) ^ 2 - 8 * (2 * b + 1) * (8 * t + 3) -
        20 * G * (8 * t + 3) ^ 2 - 60 * (8 * t + 3) ^ 2)) =
      4 * (192 * t ^ 2 * b - 960 * t ^ 2 * G - 2784 * t ^ 2 + 72 * t * b - 720 * t * G -
        2124 * t - 135 * G - 405) := by ring
  rw [show 0 - (3 * 2 ^ (m - 2)) *
        (2 * (2 * b + 1) * (8 * t + 3) +
          (2 * (2 * b + 1) * (8 * t + 3) ^ 2 - 8 * (2 * b + 1) * (8 * t + 3) -
            20 * G * (8 * t + 3) ^ 2 - 60 * (8 * t + 3) ^ 2)) =
      -(2 ^ (m - 2) * (3 * (2 * (2 * b + 1) * (8 * t + 3) +
          (2 * (2 * b + 1) * (8 * t + 3) ^ 2 - 8 * (2 * b + 1) * (8 * t + 3) -
            20 * G * (8 * t + 3) ^ 2 - 60 * (8 * t + 3) ^ 2)))) by ring, hc0]
  rw [show (2 : ℤ) ^ (m - 2) * (4 * (192 * t ^ 2 * b - 960 * t ^ 2 * G - 2784 * t ^ 2 +
        72 * t * b - 720 * t * G - 2124 * t - 135 * G - 405)) =
      2 ^ m * (192 * t ^ 2 * b - 960 * t ^ 2 * G - 2784 * t ^ 2 + 72 * t * b -
        720 * t * G - 2124 * t - 135 * G - 405) by
    rw [← mul_assoc, hpow4]]
  ring

theorem t120_preimage_coord_one {m : ℕ} (hm : 3 ≤ m) (t b : ℤ) :
    (2 : ℤ) ^ (m + 1) ∣
      (2 : ℤ) ^ (m - 1) -
        ((3 * 2 ^ (m - 2)) *
            (-(5 * (8 * t + 3)) + (-(8 * (2 * b + 1) * (8 * t + 3)) -
              26 * (8 * t + 3) ^ 2)) - 3 * 2 ^ (m - 2)) := by
  have hpow8 : (2 : ℤ) ^ (m - 2) * 8 = 2 ^ (m + 1) := by
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add, show m - 2 + 3 = m + 1 by omega]
  have hpow2 : (2 : ℤ) ^ (m - 1) = 2 ^ (m - 2) * 2 := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
  refine ⟨-(-624 * t ^ 2 - 48 * t * b - 507 * t - 18 * b - 103), ?_⟩
  have hc1 : 3 * (-(5 * (8 * t + 3)) + (-(8 * (2 * b + 1) * (8 * t + 3)) -
      26 * (8 * t + 3) ^ 2)) - 5 =
      8 * (-624 * t ^ 2 - 48 * t * b - 507 * t - 18 * b - 103) := by ring
  rw [show (2 : ℤ) ^ (m - 1) -
        ((3 * 2 ^ (m - 2)) *
            (-(5 * (8 * t + 3)) + (-(8 * (2 * b + 1) * (8 * t + 3)) -
              26 * (8 * t + 3) ^ 2)) - 3 * 2 ^ (m - 2)) =
      -(2 ^ (m - 2) * (3 * (-(5 * (8 * t + 3)) + (-(8 * (2 * b + 1) * (8 * t + 3)) -
        26 * (8 * t + 3) ^ 2)) - 5)) by
    rw [hpow2]; ring, hc1]
  rw [show (2 : ℤ) ^ (m - 2) * (8 * (-624 * t ^ 2 - 48 * t * b - 507 * t - 18 * b - 103)) =
      2 ^ (m + 1) * (-624 * t ^ 2 - 48 * t * b - 507 * t - 18 * b - 103) by
    rw [← mul_assoc, hpow8]]
  ring

theorem t120_preimage_coord_two {m : ℕ} (hm : 3 ≤ m) (t b : ℤ) :
    (2 : ℤ) ^ (m + 1) ∣
      (2 : ℤ) ^ (m - 1) -
        ((3 * 2 ^ (m - 2)) *
            (2 * (8 * t + 3) + (-(4 * (2 * b + 1) * (8 * t + 3)) +
              5 * (8 * t + 3) ^ 2)) - 3 * 2 ^ (m - 2)) := by
  have hpow8 : (2 : ℤ) ^ (m - 2) * 8 = 2 ^ (m + 1) := by
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add, show m - 2 + 3 = m + 1 by omega]
  have hpow2 : (2 : ℤ) ^ (m - 1) = 2 ^ (m - 2) * 2 := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
  refine ⟨-(120 * t ^ 2 - 24 * t * b + 84 * t - 9 * b + 14), ?_⟩
  have hc2 : 3 * (2 * (8 * t + 3) + (-(4 * (2 * b + 1) * (8 * t + 3)) +
      5 * (8 * t + 3) ^ 2)) - 5 =
      8 * (120 * t ^ 2 - 24 * t * b + 84 * t - 9 * b + 14) := by ring
  rw [show (2 : ℤ) ^ (m - 1) -
        ((3 * 2 ^ (m - 2)) *
            (2 * (8 * t + 3) + (-(4 * (2 * b + 1) * (8 * t + 3)) +
              5 * (8 * t + 3) ^ 2)) - 3 * 2 ^ (m - 2)) =
      -(2 ^ (m - 2) * (3 * (2 * (8 * t + 3) + (-(4 * (2 * b + 1) * (8 * t + 3)) +
        5 * (8 * t + 3) ^ 2)) - 5)) by
    rw [hpow2]; ring, hc2]
  rw [show (2 : ℤ) ^ (m - 2) * (8 * (120 * t ^ 2 - 24 * t * b + 84 * t - 9 * b + 14)) =
      2 ^ (m + 1) * (120 * t ^ 2 - 24 * t * b + 84 * t - 9 * b + 14) by
    rw [← mul_assoc, hpow8]]
  ring

theorem t120_uv_preimage_of_data {m : ℕ} {i F G : ℤ} (hd : Type120.Data m i F G)
    (hi : Odd i) (hF : Odd F) (hi8 : i ≡ 3 [ZMOD 8]) (hm : 3 ≤ m) :
    ∃ v : Torus (Type120.k m),
      (Type120.action hd).φuv v - v = (2 ^ (m - 1) : ℕ) • (Torus.a + Torus.b) := by
  obtain ⟨t, ht⟩ : ∃ t : ℤ, i = 8 * t + 3 := by
    rw [Int.modEq_iff_dvd] at hi8
    obtain ⟨t, ht⟩ := hi8
    exact ⟨-t, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, F = 2 * b + 1 := hF
  subst i
  subst F
  let N : ℤ := 3 * 2 ^ (m - 2)
  have hφ := t120_φuv_a_add_b hd
  refine ⟨Torus.ofInt (Type120.k m) ![0, N, N], ?_⟩
  have hv : Torus.ofInt (Type120.k m) ![0, N, N] =
      N • (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m)) := by
    rw [Torus.ofInt_eq_zsmul_gens, smul_add]
    funext j
    fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply]
  have hw : (2 ^ (m - 1) : ℕ) •
        (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m)) =
      Torus.ofInt (Type120.k m) ![0, (2 : ℤ) ^ (m - 1), (2 : ℤ) ^ (m - 1)] := by
    rw [Torus.ofInt_eq_zsmul_gens, smul_add]
    funext j
    fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply]
  rw [hv, map_zsmul, hφ, ← Torus.ofInt_zsmul, hw, ← hv, ← Torus.ofInt_sub,
    Torus.ofInt_eq_ofInt_iff]
  intro j
  fin_cases j <;> simp [N, Type120.k, Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul]
  · rw [Int.modEq_iff_dvd]
    change (2 : ℤ) ^ m ∣
      0 - (3 * 2 ^ (m - 2)) *
        (2 * (2 * b + 1) * (8 * t + 3) +
          (2 * (2 * b + 1) * (8 * t + 3) ^ 2 - 8 * (2 * b + 1) * (8 * t + 3) -
            20 * G * (8 * t + 3) ^ 2 - 60 * (8 * t + 3) ^ 2))
    exact t120_preimage_coord_zero hm t b G
  · rw [Int.modEq_iff_dvd]
    change (2 : ℤ) ^ (m + 1) ∣
      (2 : ℤ) ^ (m - 1) -
        ((3 * 2 ^ (m - 2)) *
            (-(5 * (8 * t + 3)) + (-(8 * (2 * b + 1) * (8 * t + 3)) -
              26 * (8 * t + 3) ^ 2)) - 3 * 2 ^ (m - 2))
    exact t120_preimage_coord_one hm t b
  · rw [Int.modEq_iff_dvd]
    change (2 : ℤ) ^ (m + 1) ∣
      (2 : ℤ) ^ (m - 1) -
        ((3 * 2 ^ (m - 2)) *
            (2 * (8 * t + 3) + (-(4 * (2 * b + 1) * (8 * t + 3)) +
              5 * (8 * t + 3) ^ 2)) - 3 * 2 ^ (m - 2))
    exact t120_preimage_coord_two hm t b

theorem t120_uv_preimage {m : ℕ} (hm : 3 ≤ m) :
    ∃ v : Torus (StrothTypeIndex.t120 m hm).k,
      (StrothTypeIndex.t120 m hm).action.φuv v - v =
        (2 ^ ((StrothTypeIndex.t120 m hm).n - 2) : ℕ) • (Torus.a + Torus.b) := by
  have hnexp : (StrothTypeIndex.t120 m hm).n - 2 = m - 1 := by
    have hn : (StrothTypeIndex.t120 m hm).n = m + 1 := rfl
    omega
  rw [hnexp]
  let hd : Type120.Data m (Type120.iV (m + 1)) (Type120.FV (m + 1))
      (Type120.GV (m + 1)) := Type120.data m (by omega)
  change ∃ v : Torus (Type120.k m),
    (Type120.action hd).φuv v - v =
      (2 ^ (m - 1) : ℕ) • (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m))
  exact t120_uv_preimage_of_data hd (t120_iV_odd m) (t120_FV_odd m)
    (t120_iV_modEq_eight m) hm

theorem t120_φuv_ab_half {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t120 m hm).action.φuv
        ((2 ^ ((StrothTypeIndex.t120 m hm).n - 2) : ℕ) • (Torus.a + Torus.b)) =
      -((2 ^ ((StrothTypeIndex.t120 m hm).n - 2) : ℕ) • (Torus.a + Torus.b)) := by
  obtain ⟨v, hv⟩ := t120_uv_preimage (m := m) hm
  have hsq := (StrothTypeIndex.t120 m hm).action.rels.uv_sq
  have hvv : (StrothTypeIndex.t120 m hm).action.φuv
      ((StrothTypeIndex.t120 m hm).action.φuv v) = v := by
    have := DFunLike.congr_fun hsq v
    simpa using this
  have h2 : (StrothTypeIndex.t120 m hm).action.φuv
      ((StrothTypeIndex.t120 m hm).action.φuv v - v) =
      -((StrothTypeIndex.t120 m hm).action.φuv v - v) := by
    rw [map_sub, hvv]
    abel
  rwa [hv] at h2

theorem t120_u_swaps_a_half {D : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    (dD : StrothWeakTypeData D (StrothTypeIndex.t120 m hm)) :
    dD.u⁻¹ * ((dD.a : G) ^ 2 ^ m) * dD.u = (dD.b : G) ^ 2 ^ m := by
  have h := dD.conj_ofTorus dD.u_mem dD.u_conj
    ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k))
  rw [t120_u_a_half m hm] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.a_eq] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.b_eq] at h
  exact h

theorem t120_u_fixes_ab_half {m : ℕ} {i F G : ℤ} (hd : Type120.Data m i F G)
    (hm : 1 ≤ m) :
    (Type120.action hd).φu
        ((2 ^ (m - 1) : ℕ) •
          (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m))) =
      (2 ^ (m - 1) : ℕ) •
        (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m)) := by
  have hN : (2 : ℤ) ^ (m - 1) * 2 = 2 ^ m := by
    rw [← pow_succ, show m - 1 + 1 = m by omega]
  have hva : (2 ^ (m - 1) : ℕ) • Torus.a (k := Type120.k m) =
      Torus.ofInt (Type120.k m) ![0, (2 : ℤ) ^ (m - 1), 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    funext j
    fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply]
  have hvb : (2 ^ (m - 1) : ℕ) • Torus.b (k := Type120.k m) =
      Torus.ofInt (Type120.k m) ![0, 0, (2 : ℤ) ^ (m - 1)] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    funext j
    fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply]
  have hab : (2 ^ (m - 1) : ℕ) •
        (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m)) =
      Torus.ofInt (Type120.k m)
        ![0, (2 : ℤ) ^ (m - 1), (2 : ℤ) ^ (m - 1)] := by
    rw [smul_add, hva, hvb, ← Torus.ofInt_add, Torus.ofInt_eq_ofInt_iff]
    intro j
    fin_cases j <;> simp
  change (Type120.action hd).φu
      ((2 ^ (m - 1) : ℕ) •
        (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m))) =
    (2 ^ (m - 1) : ℕ) •
      (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m))
  rw [hab]
  rw [show (Type120.action hd).φu =
      matAct (Type120.k m) (Type120.uM F) (Type120.compat_u hd) from rfl, matAct_ofInt]
  have hvec : Type120.uM F *ᵥ ![0, (2 : ℤ) ^ (m - 1), (2 : ℤ) ^ (m - 1)] =
      ![(2 : ℤ) ^ (m - 1) * (-8 * F), (2 : ℤ) ^ (m - 1),
        (2 : ℤ) ^ (m - 1)] := by
    rw [show Type120.uM F = uMat ![-1, 0, 0] (-4 * F) from rfl, uMat_mulVec]
    funext j
    fin_cases j <;> simp
    all_goals ring
  rw [hvec, Torus.ofInt_eq_ofInt_iff]
  intro j
  fin_cases j
  · change (2 : ℤ) ^ (m - 1) * (-8 * F) ≡ 0 [ZMOD 2 ^ m]
    rw [Int.modEq_iff_dvd]
    refine ⟨4 * F, ?_⟩
    rw [show (2 : ℤ) ^ (m - 1) * (-8 * F) = 2 ^ m * (-4 * F) by
      rw [show (2 : ℤ) ^ (m - 1) * (-8 * F) =
        ((2 : ℤ) ^ (m - 1) * 2) * (-4 * F) by ring, hN]]
    ring
  · exact Int.ModEq.refl _
  · exact Int.ModEq.refl _

theorem t120_d2_sq_eq {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t120 m hm)} (h : F.IsD D dD) :
    (((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t120 m hm).n - 2)) *
        (((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t120 m hm).n - 2)) =
      ((F.dA.a : G)⁻¹) ^ 2 * ((F.dA.b : G)⁻¹) ^ 2 := by
  have hexp : (StrothTypeIndex.t120 m hm).n - 2 = m - 1 := by
    have hn : (StrothTypeIndex.t120 m hm).n = m + 1 := rfl
    omega
  rw [hexp]
  set x : G := (F.dA.a : G)⁻¹ with hx
  set y : G := (F.dA.b : G)⁻¹ with hy
  set ah : G := (dD.a : G) ^ 2 ^ m with hah
  set bh : G := (dD.b : G) ^ 2 ^ m with hbh
  set ab : G := (dD.a : G) * (dD.b : G) with hab
  change ab ^ 2 ^ (m - 1) * ab ^ 2 ^ (m - 1) = x ^ 2 * y ^ 2
  haveI : IsMulCommutative D := dD.isMulCommutative
  haveI : IsMulCommutative F.A := F.dA.isMulCommutative
  have haord : orderOf (dD.a : G) = 2 ^ (m + 1) := by
    rw [Subgroup.orderOf_coe, StrothWeakTypeData.orderOf_a]
    rfl
  have hbord : orderOf (dD.b : G) = 2 ^ (m + 1) := by
    rw [Subgroup.orderOf_coe, StrothWeakTypeData.orderOf_b]
    rfl
  have hah2 : ah * ah = 1 := by
    rw [show ah * ah = (dD.a : G) ^ (2 ^ m + 2 ^ m) by
      rw [hah, ← pow_add]]
    rw [show 2 ^ m + 2 ^ m = 2 ^ (m + 1) by
      rw [← two_mul, ← pow_succ']]
    rw [← haord, pow_orderOf_eq_one]
  have hbh2 : bh * bh = 1 := by
    rw [show bh * bh = (dD.b : G) ^ (2 ^ m + 2 ^ m) by
      rw [hbh, ← pow_add]]
    rw [show 2 ^ m + 2 ^ m = 2 ^ (m + 1) by
      rw [← two_mul, ← pow_succ']]
    rw [← hbord, pow_orderOf_eq_one]
  have hah_mem_D : ah ∈ D := by
    rw [hah]
    exact D.pow_mem dD.a.2 _
  have hbh_mem_D : bh ∈ D := by
    rw [hbh]
    exact D.pow_mem dD.b.2 _
  have hahΩ : ah ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hah_mem_D hah2
  have hbhΩ : bh ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hbh_mem_D hbh2
  have hah_ofT : ah = dD.ofTorus
      ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k)) := by
    rw [hah, show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t120 m hm).k)) from dD.a_eq, ← dD.ofTorus_nsmul]
  have hbh_ofT : bh = dD.ofTorus
      ((2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k)) := by
    rw [hbh, show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t120 m hm).k)) from dD.b_eq, ← dD.ofTorus_nsmul]
  have huv_ah : dD.uv⁻¹ * ah * dD.uv = ah := by
    rw [hah_ofT]
    have hfix := dD.conj_ofTorus dD.uv_mem dD.uv_conj
      ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k))
    rwa [t120_uv_fixes_a_half m hm] at hfix
  have huv_bh : dD.uv⁻¹ * bh * dD.uv = bh := by
    rw [hbh_ofT]
    have hfix := dD.conj_ofTorus dD.uv_mem dD.uv_conj
      ((2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k))
    rwa [t120_uv_fixes_b_half m hm] at hfix
  have hahK : ah ∈ Subgroup.closure ({x ^ 2, y ^ 2} : Set G) := by
    have hfix : ah ∈ {g : G | g ∈ omegaIn 1 D ∧ dD.uv⁻¹ * g * dD.uv = g} :=
      ⟨hahΩ, huv_ah⟩
    rw [IsD.omegaIn_one_uv_fixed_eq h] at hfix
    simpa [hx, hy] using hfix
  have hbhK : bh ∈ Subgroup.closure ({x ^ 2, y ^ 2} : Set G) := by
    have hfix : bh ∈ {g : G | g ∈ omegaIn 1 D ∧ dD.uv⁻¹ * g * dD.uv = g} :=
      ⟨hbhΩ, huv_bh⟩
    rw [IsD.omegaIn_one_uv_fixed_eq h] at hfix
    simpa [hx, hy] using hfix
  have hx4 : x ^ 4 = 1 := by
    rw [hx]
    exact F.dA.pow_four_a_inv
  have hy4 : y ^ 4 = 1 := by
    rw [hy]
    exact F.dA.pow_four_b_inv
  have hx2sq : x ^ 2 * x ^ 2 = 1 := by
    rw [← pow_two, ← pow_mul, show 2 * 2 = 4 by norm_num]
    exact hx4
  have hy2sq : y ^ 2 * y ^ 2 = 1 := by
    rw [← pow_two, ← pow_mul, show 2 * 2 = 4 by norm_num]
    exact hy4
  have hcomm_xy : x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 := by
    have hx2A : x ^ 2 ∈ F.A := by
      rw [hx]
      exact F.A.pow_mem (F.A.inv_mem F.dA.a.2) 2
    have hy2A : y ^ 2 ∈ F.A := by
      rw [hy]
      exact F.A.pow_mem (F.A.inv_mem F.dA.b.2) 2
    exact mul_comm_mem_of_isMulCommutative (D := F.A) hx2A hy2A
  have hXXY : x ^ 2 * (x ^ 2 * y ^ 2) = y ^ 2 := by
    rw [← mul_assoc, hx2sq, one_mul]
  have hYXY : y ^ 2 * (x ^ 2 * y ^ 2) = x ^ 2 := by
    rw [← mul_assoc, hcomm_xy.symm, mul_assoc, hy2sq, mul_one]
  have hXYXY : (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2) = 1 := by
    calc (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2)
        = x ^ 2 * (y ^ 2 * x ^ 2) * y ^ 2 := by group
      _ = x ^ 2 * (x ^ 2 * y ^ 2) * y ^ 2 := by rw [hcomm_xy.symm]
      _ = (x ^ 2 * x ^ 2) * (y ^ 2 * y ^ 2) := by group
      _ = 1 := by rw [hx2sq, hy2sq, mul_one]
  have hXinv : (x ^ 2)⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right hx2sq
  have hYinv : (y ^ 2)⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right hy2sq
  have hXYinv : (x ^ 2 * y ^ 2)⁻¹ = x ^ 2 * y ^ 2 :=
    inv_eq_of_mul_eq_one_right hXYXY
  have hKsub : ∀ z ∈ Subgroup.closure ({x ^ 2, y ^ 2} : Set G),
      z = 1 ∨ z = x ^ 2 ∨ z = y ^ 2 ∨ z = x ^ 2 * y ^ 2 := by
    intro z hz
    refine Subgroup.closure_induction (p := fun z _ =>
      z = 1 ∨ z = x ^ 2 ∨ z = y ^ 2 ∨ z = x ^ 2 * y ^ 2) ?_ ?_ ?_ ?_ hz
    · intro u hu
      rcases hu with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · intro a b _ _ iha ihb
      rcases iha with rfl | rfl | rfl | rfl <;>
        rcases ihb with rfl | rfl | rfl | rfl <;>
        simp [hx2sq, hy2sq, hcomm_xy.symm, hXXY, hYXY, hXYXY, mul_assoc]
    · intro a _ iha
      rcases iha with rfl | rfl | rfl | rfl <;>
        simp [hXinv, hYinv, hXYinv]
  have hux : F.dA.u⁻¹ * x * F.dA.u = y := by
    rw [hx, hy]
    exact StrothWeakTypeData.u_conj_a_inv F.dA
  have huy : F.dA.u⁻¹ * y * F.dA.u = x := by
    have hu : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
    calc F.dA.u⁻¹ * y * F.dA.u
        = F.dA.u⁻¹ * (F.dA.u⁻¹ * x * F.dA.u) * F.dA.u := by rw [hux]
      _ = (F.dA.u⁻¹ * F.dA.u⁻¹) * x * (F.dA.u * F.dA.u) := by group
      _ = x := by rw [hu, F.dA.u_sq, one_mul, mul_one]
  have hux2 : F.dA.u⁻¹ * x ^ 2 * F.dA.u = y ^ 2 := by
    calc F.dA.u⁻¹ * x ^ 2 * F.dA.u
        = (F.dA.u⁻¹ * x * F.dA.u) ^ 2 := by
            simpa [inv_inv] using
              (conj_pow (a := F.dA.u⁻¹) (b := x) (i := 2)).symm
      _ = y ^ 2 := by rw [hux]
  have huy2 : F.dA.u⁻¹ * y ^ 2 * F.dA.u = x ^ 2 := by
    calc F.dA.u⁻¹ * y ^ 2 * F.dA.u
        = (F.dA.u⁻¹ * y * F.dA.u) ^ 2 := by
            simpa [inv_inv] using
              (conj_pow (a := F.dA.u⁻¹) (b := y) (i := 2)).symm
      _ = x ^ 2 := by rw [huy]
  have hufix : F.dA.u⁻¹ * (x ^ 2 * y ^ 2) * F.dA.u = x ^ 2 * y ^ 2 := by
    calc F.dA.u⁻¹ * (x ^ 2 * y ^ 2) * F.dA.u
        = (F.dA.u⁻¹ * x ^ 2 * F.dA.u) * (F.dA.u⁻¹ * y ^ 2 * F.dA.u) := by group
      _ = y ^ 2 * x ^ 2 := by rw [hux2, huy2]
      _ = x ^ 2 * y ^ 2 := hcomm_xy.symm
  have hswap_d : dD.u⁻¹ * ah * dD.u = bh := by
    simpa [hah, hbh] using t120_u_swaps_a_half hm dD
  have hswap : F.dA.u⁻¹ * ah * F.dA.u = bh := by
    rw [← h.u_eq]
    exact hswap_d
  have hu_bh : F.dA.u⁻¹ * bh * F.dA.u = ah := by
    have hu : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
    calc F.dA.u⁻¹ * bh * F.dA.u
        = F.dA.u⁻¹ * (F.dA.u⁻¹ * ah * F.dA.u) * F.dA.u := by rw [hswap]
      _ = (F.dA.u⁻¹ * F.dA.u⁻¹) * ah * (F.dA.u * F.dA.u) := by group
      _ = ah := by rw [hu, F.dA.u_sq, one_mul, mul_one]
  have hltpow : 2 ^ m < 2 ^ (m + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hah_ne_one : ah ≠ 1 := by
    have hlt : 2 ^ m < orderOf (dD.a : G) := by
      simpa [haord] using hltpow
    have h := pow_ne_one_of_lt_orderOf (x := (dD.a : G)) (n := 2 ^ m)
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hlt
    simpa [hah] using h
  have hbh_ne_one : bh ≠ 1 := by
    have hlt : 2 ^ m < orderOf (dD.b : G) := by
      simpa [hbord] using hltpow
    have h := pow_ne_one_of_lt_orderOf (x := (dD.b : G)) (n := 2 ^ m)
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hlt
    simpa [hbh] using h
  have hua_ne : (2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k) ≠
      (2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k) := by
    have hva : (2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k) =
        Torus.ofInt (StrothTypeIndex.t120 m hm).k ![0, (2 : ℤ) ^ m, 0] := by
      rw [Torus.ofInt_eq_zsmul_gens]
      funext j
      fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply]
    have hvb : (2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k) =
        Torus.ofInt (StrothTypeIndex.t120 m hm).k ![0, 0, (2 : ℤ) ^ m] := by
      rw [Torus.ofInt_eq_zsmul_gens]
      funext j
      fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply]
    intro htor
    rw [hva, hvb, Torus.ofInt_eq_ofInt_iff] at htor
    have h2 := htor 2
    rw [show (StrothTypeIndex.t120 m hm).k 2 = m + 1 from rfl] at h2
    rw [Int.modEq_iff_dvd] at h2
    simp at h2
    have h2' : (2 : ℕ) ^ (m + 1) ∣ 2 ^ m := by exact_mod_cast h2
    exact Nat.not_dvd_of_pos_of_lt (by positivity)
      (Nat.pow_lt_pow_right (by norm_num) (by omega)) h2'
  have hahb_ne : ah ≠ bh := by
    intro heq
    have htor : (2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t120 m hm).k) =
        (2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t120 m hm).k) := by
      apply dD.ofTorus_inj
      rw [← hah_ofT, ← hbh_ofT]
      exact heq
    exact hua_ne htor
  have hah_ne_xy : ah ≠ x ^ 2 * y ^ 2 := by
    intro hxy
    have hbh_eq : bh = x ^ 2 * y ^ 2 := by
      rw [← hswap, hxy, hufix]
    exact hahb_ne (hxy.trans hbh_eq.symm)
  have hbh_ne_xy : bh ≠ x ^ 2 * y ^ 2 := by
    intro hxy
    have hah_eq : ah = x ^ 2 * y ^ 2 := by
      rw [← hu_bh, hxy, hufix]
    exact hahb_ne (hah_eq.trans hxy.symm)
  have hcomm_ab : Commute (dD.a : G) (dD.b : G) :=
    mul_comm_mem_of_isMulCommutative (D := D) dD.a.2 dD.b.2
  have hLHS : ab ^ 2 ^ (m - 1) * ab ^ 2 ^ (m - 1) = ah * bh := by
    have hpow : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
      rw [← two_mul, ← pow_succ', show m - 1 + 1 = m by omega]
    calc ab ^ 2 ^ (m - 1) * ab ^ 2 ^ (m - 1)
        = ab ^ (2 ^ (m - 1) + 2 ^ (m - 1)) := (pow_add ab _ _).symm
      _ = ab ^ 2 ^ m := by rw [hpow]
      _ = (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m := by
            rw [hab]
            exact hcomm_ab.mul_pow _
      _ = ah * bh := by rw [← hah, ← hbh]
  have hmain : ah * bh = x ^ 2 * y ^ 2 := by
    rcases hKsub ah hahK with hah1 | hahx | hahy | hahxy
    · exact absurd hah1 hah_ne_one
    · rcases hKsub bh hbhK with hbh1 | hbhx | hbhy | hbhxy
      · exact absurd hbh1 hbh_ne_one
      · exact absurd (hahx.trans hbhx.symm) hahb_ne
      · rw [hahx, hbhy]
      · exact absurd hbhxy hbh_ne_xy
    · rcases hKsub bh hbhK with hbh1 | hbhx | hbhy | hbhxy
      · exact absurd hbh1 hbh_ne_one
      · rw [hahy, hbhx, hcomm_xy.symm]
      · exact absurd (hahy.trans hbhy.symm) hahb_ne
      · exact absurd hbhxy hbh_ne_xy
    · exact absurd hahxy hah_ne_xy
  exact hLHS.trans hmain

theorem t120_d2_ofTorus {D : Subgroup G} {m : ℕ} {hm : 3 ≤ m}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t120 m hm)} :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t120 m hm).n - 2) =
      dD.ofTorus ((2 ^ ((StrothTypeIndex.t120 m hm).n - 2) : ℕ) •
        (Torus.a (k := (StrothTypeIndex.t120 m hm).k) +
          Torus.b (k := (StrothTypeIndex.t120 m hm).k))) := by
  rw [show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t120 m hm).k)) from dD.a_eq,
    show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t120 m hm).k)) from dD.b_eq,
    ← dD.ofTorus_add, ← dD.ofTorus_nsmul]

theorem t120_d2_mem_A {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t120 m hm)} (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t120 m hm).n - 2) ∈ F.A := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t120 m hm).n - 2)
  let x : G := (F.dA.a : G)⁻¹
  let y : G := (F.dA.b : G)⁻¹
  change d2 ∈ F.A
  haveI : IsMulCommutative D := dD.isMulCommutative
  haveI : IsMulCommutative F.A := F.dA.isMulCommutative
  have hd2D : d2 ∈ D := by
    dsimp only [d2]
    exact D.pow_mem (D.mul_mem dD.a.2 dD.b.2) _
  have hxA : x ∈ F.A := by dsimp only [x]; exact F.A.inv_mem F.dA.a.2
  have hyA : y ∈ F.A := by dsimp only [y]; exact F.A.inv_mem F.dA.b.2
  have hxyA : x * y ∈ F.A := F.A.mul_mem hxA hyA
  have hxyD : x * y ∈ D := h.A_le hxyA
  have hxy_sq : (x * y) * (x * y) = x ^ 2 * y ^ 2 := by
    have hxy_comm : x * y = y * x :=
      mul_comm_mem_of_isMulCommutative (D := F.A) hxA hyA
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy_comm]
      _ = (x * x) * (y * y) := by group
      _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]
  have hd2sq : d2 * d2 = x ^ 2 * y ^ 2 := by
    simpa [d2, x, y] using t120_d2_sq_eq (m := m) (dD := dD) hm h
  have hcomm : Commute d2 (x * y) :=
    mul_comm_mem_of_isMulCommutative (D := D) hd2D hxyD
  have hcomm_inv : Commute d2 (x * y)⁻¹ := hcomm.inv_right
  have hz2 : (d2 * (x * y)⁻¹) * (d2 * (x * y)⁻¹) = 1 := by
    calc (d2 * (x * y)⁻¹) * (d2 * (x * y)⁻¹)
        = d2 * ((x * y)⁻¹ * d2) * (x * y)⁻¹ := by group
      _ = d2 * (d2 * (x * y)⁻¹) * (x * y)⁻¹ := by rw [hcomm_inv.eq.symm]
      _ = (d2 * d2) * ((x * y)⁻¹ * (x * y)⁻¹) := by group
      _ = (x ^ 2 * y ^ 2) * (((x * y) * (x * y))⁻¹) := by
            rw [hd2sq, ← _root_.mul_inv_rev]
      _ = (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2)⁻¹ := by rw [hxy_sq]
      _ = 1 := mul_inv_cancel _
  have hzA : d2 * (x * y)⁻¹ ∈ F.A :=
    h.mem_A_of_mul_self (D.mul_mem hd2D (D.inv_mem hxyD)) hz2
  have hd2_eq : d2 = (d2 * (x * y)⁻¹) * (x * y) := by group
  rw [hd2_eq]
  exact F.A.mul_mem hzA hxyA

theorem t120_d2_eq_xy {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t120 m hm)} (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t120 m hm).n - 2) =
        F.dA.toConfig.x * F.dA.toConfig.y ∨
      ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t120 m hm).n - 2) =
        (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t120 m hm).n - 2)
  let w : Torus (StrothTypeIndex.t120 m hm).k :=
    (2 ^ ((StrothTypeIndex.t120 m hm).n - 2) : ℕ) • (Torus.a + Torus.b)
  change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
    d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹
  have hd2A : d2 ∈ F.A := by
    simpa [d2] using t120_d2_mem_A (m := m) (dD := dD) hm h
  have hd2D : d2 ∈ D := by
    dsimp only [d2]
    exact D.pow_mem (D.mul_mem dD.a.2 dD.b.2) _
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t120_d2_ofTorus (m := m) (hm := hm) (dD := dD)
  have hexp : (StrothTypeIndex.t120 m hm).n - 2 = m - 1 := by
    have hn : (StrothTypeIndex.t120 m hm).n = m + 1 := rfl
    omega
  have hφu : (StrothTypeIndex.t120 m hm).action.φu w = w := by
    dsimp only [w]
    rw [hexp]
    let hd : Type120.Data m (Type120.iV (m + 1)) (Type120.FV (m + 1))
        (Type120.GV (m + 1)) := Type120.data m (by omega)
    change (Type120.action hd).φu
        ((2 ^ (m - 1) : ℕ) •
          (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m))) =
      (2 ^ (m - 1) : ℕ) •
        (Torus.a (k := Type120.k m) + Torus.b (k := Type120.k m))
    exact t120_u_fixes_ab_half hd (by omega)
  have hφuv : (StrothTypeIndex.t120 m hm).action.φuv w = -w := by
    dsimp only [w]
    exact t120_φuv_ab_half (m := m) hm
  have hdu : dD.u⁻¹ * d2 * dD.u = d2 := by
    rw [hd2_ofT]
    have hconj := dD.conj_ofTorus dD.u_mem dD.u_conj w
    rwa [hφu] at hconj
  have hduv : dD.uv⁻¹ * d2 * dD.uv = d2⁻¹ := by
    rw [hd2_ofT]
    have hconj := dD.conj_ofTorus dD.uv_mem dD.uv_conj w
    rw [hφuv, dD.ofTorus_neg] at hconj
    exact hconj
  have hduA : F.dA.u⁻¹ * d2 * F.dA.u = d2 := by
    rw [← h.u_eq]
    exact hdu
  have hduvA : F.dA.uv⁻¹ * d2 * F.dA.uv = d2⁻¹ := by
    rw [← h.uv_eq]
    exact hduv
  obtain ⟨δ, hδ⟩ := F.dA.exists_ofTorus hd2A
  have hδ2 : δ + δ = (2 : ℕ) • Torus.a + (2 : ℕ) • Torus.b := by
    apply F.dA.ofTorus_inj
    rw [F.dA.ofTorus_add, F.dA.ofTorus_add, F.dA.ofTorus_nsmul, F.dA.ofTorus_nsmul]
    rw [← hδ]
    have hd2sq : d2 * d2 =
        ((F.dA.a : G)⁻¹) ^ 2 * ((F.dA.b : G)⁻¹) ^ 2 := by
      simpa [d2] using t120_d2_sq_eq (m := m) (dD := dD) hm h
    rw [hd2sq, F.a_inv_sq, F.b_inv_sq]
    rfl
  have hδu : (StrothTypeIndex.t100 1).action.φu δ = δ := by
    apply F.dA.ofTorus_inj
    have hconj := F.dA.conj_ofTorus F.dA.u_mem F.dA.u_conj δ
    rw [← hconj, ← hδ]
    exact hduA
  have hδuv : (StrothTypeIndex.t100 1).action.φuv δ = -δ := by
    apply F.dA.ofTorus_inj
    rw [F.dA.ofTorus_neg]
    have hconj := F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj δ
    rw [← hconj, ← hδ]
    exact hduvA
  have hxy : F.dA.toConfig.x * F.dA.toConfig.y =
      F.dA.ofTorus (-(Torus.a + Torus.b)) := by
    rw [StrothWeakTypeData.toConfig_x, StrothWeakTypeData.toConfig_y,
      neg_add, F.dA.ofTorus_add, F.dA.ofTorus_neg, F.dA.ofTorus_neg,
      ← F.dA.a_eq, ← F.dA.b_eq]
  rcases Stroth43Fus.t100_one_xy δ hδ2 hδu hδuv with hδab | hδab
  · right
    rw [hδ, hδab, hxy, ← F.dA.ofTorus_neg, neg_neg]
  · left
    rw [hδ, hδab, hxy]

theorem t120_isConj_uv_xyuv {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t120 m hm)} (h : F.IsD D dD) :
    IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv) := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t120 m hm).n - 2)
  let w : Torus (StrothTypeIndex.t120 m hm).k :=
    (2 ^ ((StrothTypeIndex.t120 m hm).n - 2) : ℕ) • (Torus.a + Torus.b)
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t120_d2_ofTorus (m := m) (hm := hm) (dD := dD)
  have hd2 : d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
    have h := t120_d2_eq_xy (m := m) (dD := dD) hm h
    change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ at h
    exact h
  obtain ⟨v, hv⟩ := t120_uv_preimage (m := m) hm
  have hφ : dD.ofTorus ((StrothTypeIndex.t120 m hm).action.φuv v - v) = d2 := by
    rw [hv, hd2_ofT]
  exact isConj_uv_xyuv_of_d2 (τ := StrothTypeIndex.t120 m hm) h hd2 hφ

end StrothFrame.IsD

end CFSG.CGT.Stroth77
