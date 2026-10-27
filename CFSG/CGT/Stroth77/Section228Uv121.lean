module

public import CFSG.CGT.Stroth77.Section228Uv

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

open Matrix

theorem t121_uvM_row0_mod4 {m : ℕ} (hm : 3 ≤ m) :
    ((Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) 0 1 +
      Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) 0 2 : ℤ)
      : ZMod 4) = 0 := by
  simp [Type121.uvM, Type121.tM, Type121.uvA, Type121.ρM, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, ofCols, ofCols_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [Type120.iV_cast (n := m + 1) (k := 2) (by omega)]
  rw [Type120.FV_cast (n := m + 1) (k := 2) (by omega)]
  rw [Type120.GV_cast (n := m + 1) (k := 2) (by omega)]
  have htwo : ((2 : ZMod 4) ^ m) = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : 2 ≤ m)
  rw [htwo]
  have h3 : ((3 : ZMod 4)⁻¹) = 3 := ZMod.inv_eq_of_mul_eq_one 4 3 3 (by decide)
  rw [h3]
  decide

theorem t121_uvM_row1_mod8 {m : ℕ} (hm : 3 ≤ m) :
    ((Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) 1 1 +
      Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) 1 2 : ℤ)
      : ZMod 8) = 7 := by
  simp [Type121.uvM, Type121.tM, Type121.uvA, Type121.ρM, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, ofCols, ofCols_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [Type120.iV_cast (n := m + 1) (k := 3) (by omega)]
  rw [Type120.FV_cast (n := m + 1) (k := 3) (by omega)]
  have htwo : ((2 : ZMod 8) ^ m) = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : 3 ≤ m)
  rw [htwo]
  have h3 : ((3 : ZMod 8)⁻¹) = 3 := ZMod.inv_eq_of_mul_eq_one 8 3 3 (by decide)
  rw [h3]
  decide

theorem t121_uvM_row2_mod8 {m : ℕ} (hm : 3 ≤ m) :
    ((Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) 2 1 +
      Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) 2 2 : ℤ)
      : ZMod 8) = 7 := by
  simp [Type121.uvM, Type121.tM, Type121.uvA, Type121.ρM, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, ofCols, ofCols_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [Type120.iV_cast (n := m + 1) (k := 3) (by omega)]
  rw [Type120.FV_cast (n := m + 1) (k := 3) (by omega)]
  have htwo : ((2 : ZMod 8) ^ m) = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : 3 ≤ m)
  rw [htwo]
  have h3 : ((3 : ZMod 8)⁻¹) = 3 := ZMod.inv_eq_of_mul_eq_one 8 3 3 (by decide)
  rw [h3]
  decide

theorem t121_preimage_case0 (m : ℕ) (hm : 3 ≤ m) (X : ℤ) (h0 : (X : ZMod 4) = 0) :
    (3 * 2 ^ (m - 2) : ℕ) * (X : ZMod (2 ^ m)) = 0 := by
  have h4 : (4 : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X 4).mp h0
  obtain ⟨k, hk⟩ := h4
  have hdiv : ((2 : ℤ) ^ m) ∣ 3 * 2 ^ (m - 2) * X := by
    rw [hk]
    have hm2 : (2 : ℤ) ^ m = 2 ^ (m - 2) * 4 := by
      rw [show m = m - 2 + 2 by omega, pow_add]
      norm_num
    rw [hm2]
    ring_nf
    exact ⟨3 * k, by ring⟩
  rw [show ((3 * 2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) = ((3 * 2 ^ (m - 2) : ℤ) : ZMod (2 ^ m)) by
    norm_num]
  rw [← Int.cast_mul]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact hdiv

theorem t121_preimage_case0_zmod (m : ℕ) (hm : 3 ≤ m) (X : ℤ) (h0 : (X : ZMod 4) = 0) :
    (3 * 2 ^ (m - 2) : ZMod (2 ^ m)) * (X : ZMod (2 ^ m)) = 0 := by
  have h := t121_preimage_case0 m hm X h0
  convert h using 2 <;> push_cast <;> ring

theorem t121_preimage_case1 (m : ℕ) (hm : 3 ≤ m) (X : ℤ) (h1 : (X : ZMod 8) = 7) :
    (3 * 2 ^ (m - 2) : ℕ) * ((X : ZMod (2 ^ (m + 1))) - 1) =
      ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (m + 1))) := by
  have h8 : X ≡ 7 [ZMOD 8] := (ZMod.intCast_eq_intCast_iff X 7 8).mp h1
  have hdvd : (8 : ℤ) ∣ X - 7 := by
    rw [Int.modEq_iff_dvd] at h8
    rw [show 7 - X = -(X - 7) by ring] at h8
    exact dvd_neg.mp h8
  obtain ⟨k, hk⟩ := hdvd
  have hdiv : ((2 : ℤ) ^ (m + 1)) ∣ (3 * 2 ^ (m - 2) * (X - 1) - 2 ^ (m - 1)) := by
    rw [show X - 1 = (X - 7) + 6 by ring, hk]
    have hpow : (2 : ℤ) ^ (m + 1) = 2 ^ (m - 2) * 8 := by
      rw [show m + 1 = m - 2 + 3 by omega, pow_add]
      norm_num
    have hpow2 : (2 : ℤ) ^ (m - 1) = 2 ^ (m - 2) * 2 := by
      rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
    rw [hpow, hpow2]
    refine ⟨3 * k + 2, ?_⟩
    ring
  rw [show ((3 * 2 ^ (m - 2) : ℕ) : ZMod (2 ^ (m + 1))) = ((3 * 2 ^ (m - 2) : ℤ) : ZMod _) by
    norm_num]
  rw [show ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (m + 1))) = ((2 ^ (m - 1) : ℤ) : ZMod _) by
    norm_num]
  rw [show ((3 * 2 ^ (m - 2) : ℤ) : ZMod (2 ^ (m + 1))) * ((X : ZMod (2 ^ (m + 1))) - 1)
      = (((3 * 2 ^ (m - 2) * (X - 1) : ℤ)) : ZMod (2 ^ (m + 1))) by
    push_cast
    ring]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  rw [show (2 : ℤ) ^ (m - 1) - 3 * 2 ^ (m - 2) * (X - 1)
      = -(3 * 2 ^ (m - 2) * (X - 1) - 2 ^ (m - 1)) by ring]
  exact dvd_neg.mpr hdiv

theorem t121_preimage_case1_any (m : ℕ) (hm : 3 ≤ m) (a : ZMod (2 ^ (m + 1))) (X : ℤ)
    (ha : a = ((3 * 2 ^ (m - 2) : ℕ) : ZMod (2 ^ (m + 1))))
    (h1 : (X : ZMod 8) = 7) :
    a * (X : ZMod (2 ^ (m + 1))) - a = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (m + 1))) := by
  rw [ha]
  simpa [mul_sub] using t121_preimage_case1 m hm X h1

theorem t121_preimage_case1_zmod (m : ℕ) (hm : 3 ≤ m) (X : ℤ) (h1 : (X : ZMod 8) = 7) :
    (3 * 2 ^ (m - 2) : ZMod (2 ^ (m + 1))) * (X : ZMod (2 ^ (m + 1))) -
      (3 * 2 ^ (m - 2) : ZMod (2 ^ (m + 1))) =
      (2 : ZMod (2 ^ (m + 1))) ^ (m - 1) := by
  have h := t121_preimage_case1 m hm X h1
  convert h using 2 <;> push_cast <;> ring

theorem t121_uv_preimage_type121 {m : ℕ} (hm : 3 ≤ m) :
    ∃ v : Torus (Type121.k m),
      (Type121.action (Type121.data m (by omega))).φuv v - v =
        (2 ^ (m - 1) : ℕ) • (Torus.a + Torus.b (k := Type121.k m)) := by
  let v : Torus (Type121.k m) :=
    (3 * 2 ^ (m - 2) : ℕ) • (Torus.a + Torus.b)
  refine ⟨v, ?_⟩
  dsimp only [Type121.action, SigmaFourAction.ofMatEq, SigmaFourAction.φuv]
  dsimp only [v]
  rw [map_nsmul, map_add]
  rw [matAct_gen_eq, matAct_gen_eq]
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply, zsmul_eq_mul, Torus.a, Torus.b]
  · rw [← mul_add, ← Int.cast_add]
    exact t121_preimage_case0_zmod m hm _ (t121_uvM_row0_mod4 hm)
  · rw [← mul_add, ← Int.cast_add]
    exact t121_preimage_case1_zmod m hm _ (t121_uvM_row1_mod8 hm)
  · rw [← mul_add, ← Int.cast_add]
    exact t121_preimage_case1_zmod m hm _ (t121_uvM_row2_mod8 hm)

theorem t121_u_a_half_torus {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t121 m hm).action.φu
        ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t121 m hm).k)) =
      (2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t121 m hm).k) := by
  show (Type121.action (Type121.data m (by omega))).φu
      ((2 ^ m : ℕ) • Torus.a (k := Type121.k m)) =
    (2 ^ m : ℕ) • Torus.b (k := Type121.k m)
  dsimp only [Type121.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu]
  rw [map_nsmul, matAct_gen_eq]
  simp [Type121.uM, uMat, ofCols, ofCols_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply, zsmul_eq_mul]
  · have hzero : ((2 : ZMod (2 ^ Type121.k m 0)) ^ m) = 0 := by
      rw [show (2 : ZMod (2 ^ Type121.k m 0)) =
        ((2 : ℕ) : ZMod (2 ^ Type121.k m 0)) by norm_num]
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self _
    rw [hzero]
    ring

theorem t121_uv_fixes_a_half_torus {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t121 m hm).action.φuv
        ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t121 m hm).k)) =
      (2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t121 m hm).k) := by
  show (Type121.action (Type121.data m (by omega))).φuv
      ((2 ^ m : ℕ) • Torus.a (k := Type121.k m)) =
    (2 ^ m : ℕ) • Torus.a (k := Type121.k m)
  dsimp only [Type121.action, SigmaFourAction.ofMatEq, SigmaFourAction.φuv]
  rw [map_nsmul, matAct_gen_eq]
  simp [Type121.uvM, Type121.uvA, Type121.ρM, Type121.tM, uMat, ofCols, ofCols_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply, zsmul_eq_mul]
  · have hzero : ((2 : ZMod (2 ^ Type121.k m 0)) ^ m) = 0 := by
      rw [show (2 : ZMod (2 ^ Type121.k m 0)) =
        ((2 : ℕ) : ZMod (2 ^ Type121.k m 0)) by norm_num]
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self _
    rw [hzero]
    ring
  · obtain ⟨hi, -, -, -, -⟩ := Type121.data m (by omega : 1 ≤ m)
    have hodd : Odd (-5 * Type120.iV (m + 1)) := by
      rw [hi]
      exact ⟨-20 * Type120.GV (m + 1) - 48, by ring⟩
    have h := intCast_mul_two_pow_pred_of_odd (n := m + 1) (z := -5 * Type120.iV (m + 1)) hodd
    have h' : ((↑(-5 * Type120.iV (m + 1) * 2 ^ m) : ZMod (2 ^ (m + 1)))) =
        (2 : ZMod (2 ^ (m + 1))) ^ m := by
      simpa only [Nat.add_sub_cancel] using h
    have hpow : ((2 : ZMod (2 ^ (m + 1))) ^ m) =
        ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    change -(((2 : ZMod (2 ^ (m + 1))) ^ m) *
        (5 * ↑(Type120.iV (m + 1)))) = (2 : ZMod (2 ^ (m + 1))) ^ m
    rw [hpow] at h'
    rw [hpow]
    rw [show -(((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) *
          (5 * ↑(Type120.iV (m + 1))))
        = ((↑(-5 * Type120.iV (m + 1) * 2 ^ m) : ZMod (2 ^ (m + 1)))) by
      push_cast
      ring]
    exact h'
  · have hzero : ((2 : ZMod (2 ^ Type121.k m 2)) ^ (m + 1)) = 0 := by
      rw [show (2 : ZMod (2 ^ Type121.k m 2)) =
        ((2 : ℕ) : ZMod (2 ^ Type121.k m 2)) by norm_num]
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self _
    have h2m2 : ((2 : ZMod (2 ^ Type121.k m 2)) ^ m) *
        (2 : ZMod (2 ^ Type121.k m 2)) = 0 := by
      rw [← pow_succ, hzero]
    have h2mm : ((2 : ZMod (2 ^ Type121.k m 2)) ^ m) *
        ((2 : ZMod (2 ^ Type121.k m 2)) ^ m) = 0 := by
      calc ((2 : ZMod (2 ^ Type121.k m 2)) ^ m) *
            ((2 : ZMod (2 ^ Type121.k m 2)) ^ m)
          = (2 : ZMod (2 ^ Type121.k m 2)) ^ (m + m) := by rw [← pow_add]
        _ = (2 : ZMod (2 ^ Type121.k m 2)) ^ ((m + 1) + (m - 1)) := by
              rw [show m + m = (m + 1) + (m - 1) by omega]
        _ = (2 : ZMod (2 ^ Type121.k m 2)) ^ (m + 1) *
              (2 : ZMod (2 ^ Type121.k m 2)) ^ (m - 1) := pow_add _ _ _
        _ = 0 := by rw [hzero, zero_mul]
    rw [mul_add, ← mul_assoc, ← pow_succ, hzero, zero_mul, h2mm]
    ring

theorem t121_u_add_b_torus {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t121 m hm).action.φu
        (Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
          Torus.b (k := (StrothTypeIndex.t121 m hm).k)) =
      Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
          Torus.b (k := (StrothTypeIndex.t121 m hm).k) -
        (8 * Type120.FV (m + 1)) • Torus.c (k := (StrothTypeIndex.t121 m hm).k) := by
  show (Type121.action (Type121.data m (by omega))).φu
        (Torus.a (k := Type121.k m) + Torus.b (k := Type121.k m)) =
      Torus.a (k := Type121.k m) + Torus.b (k := Type121.k m) -
        (8 * Type120.FV (m + 1)) • Torus.c (k := Type121.k m)
  dsimp only [Type121.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu]
  rw [map_add, matAct_gen_eq, matAct_gen_eq]
  simp [Type121.uM, uMat, ofCols, ofCols_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply, zsmul_eq_mul] <;> ring

theorem t121_u_fixes_ab_half_torus {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t121 m hm).action.φu
        ((2 ^ (m - 1) : ℕ) • (Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
          Torus.b (k := (StrothTypeIndex.t121 m hm).k))) =
      (2 ^ (m - 1) : ℕ) • (Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
          Torus.b (k := (StrothTypeIndex.t121 m hm).k)) := by
  rw [map_nsmul, t121_u_add_b_torus (m := m) hm, smul_sub]
  have hc : (2 ^ (m - 1) : ℕ) •
      ((8 * Type120.FV (m + 1) : ℤ) •
        Torus.c (k := (StrothTypeIndex.t121 m hm).k)) = 0 := by
    show (2 ^ (m - 1) : ℕ) •
      ((8 * Type120.FV (m + 1) : ℤ) • Torus.c (k := Type121.k m)) = 0
    funext i
    fin_cases i <;> simp [Torus.c, gen, Pi.single_apply, nsmul_eq_mul, zsmul_eq_mul]
    · push_cast
      have hzero : ((2 : ZMod (2 ^ m)) ^ m) = 0 := by
        rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) from by norm_num]
        rw [← Nat.cast_pow, ZMod.natCast_self]
      calc (2 : ZMod (2 ^ m)) ^ (m - 1) * (8 * (Type120.FV (m + 1) : ZMod (2 ^ m)))
          = (2 : ZMod (2 ^ m)) ^ (m + 2) * (Type120.FV (m + 1) : ZMod (2 ^ m)) := by
              rw [show (8 : ZMod (2 ^ m)) = (2 : ZMod (2 ^ m)) ^ 3 by norm_num,
                ← mul_assoc, ← pow_add, show (m - 1) + 3 = m + 2 by omega]
        _ = ((2 : ZMod (2 ^ m)) ^ m * (2 : ZMod (2 ^ m)) ^ 2) *
              (Type120.FV (m + 1) : ZMod (2 ^ m)) := by
              rw [show m + 2 = m + 2 by rfl, pow_add]
        _ = 0 := by rw [hzero, zero_mul]; ring
  rw [hc, sub_zero]


theorem t121_uv_preimage {m : ℕ} (hm : 3 ≤ m) :
    ∃ v : Torus (StrothTypeIndex.t121 m hm).k,
      (StrothTypeIndex.t121 m hm).action.φuv v - v =
        (2 ^ (m - 1) : ℕ) •
          (Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
            Torus.b (k := (StrothTypeIndex.t121 m hm).k)) := by
  change ∃ v : Torus (Type121.k m),
      (Type121.action (Type121.data m (by omega))).φuv v - v =
        (2 ^ (m - 1) : ℕ) •
          (Torus.a (k := Type121.k m) + Torus.b (k := Type121.k m))
  exact t121_uv_preimage_type121 (m := m) hm

theorem t121_u_swaps_a_half {D : Subgroup G} {m : ℕ} {hm : 3 ≤ m}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t121 m hm)} :
    dD.u⁻¹ * (dD.a : G) ^ 2 ^ m * dD.u = (dD.b : G) ^ 2 ^ m := by
  have h := dD.conj_ofTorus dD.u_mem dD.u_conj
    ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t121 m hm).k))
  rw [t121_u_a_half_torus (m := m) hm] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.a_eq] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.b_eq] at h
  exact h

theorem t121_uv_fixes_a_half {D : Subgroup G} {m : ℕ} {hm : 3 ≤ m}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t121 m hm)} :
    dD.uv⁻¹ * (dD.a : G) ^ 2 ^ m * dD.uv = (dD.a : G) ^ 2 ^ m := by
  have h := dD.conj_ofTorus dD.uv_mem dD.uv_conj
    ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t121 m hm).k))
  rw [t121_uv_fixes_a_half_torus (m := m) hm] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.a_eq] at h
  exact h

theorem t121_uv_fixes_b_half {D : Subgroup G} {m : ℕ} {hm : 3 ≤ m}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t121 m hm)} :
    dD.uv⁻¹ * (dD.b : G) ^ 2 ^ m * dD.uv = (dD.b : G) ^ 2 ^ m := by
  have hswap := t121_u_swaps_a_half (dD := dD) (m := m) (hm := hm)
  have hfixa := t121_uv_fixes_a_half (dD := dD) (m := m) (hm := hm)
  have h1 : dD.uv⁻¹ * dD.u⁻¹ = dD.u⁻¹ * dD.uv⁻¹ := by
    rw [← _root_.mul_inv_rev, ← dD.uv_comm_u, _root_.mul_inv_rev]
  calc dD.uv⁻¹ * (dD.b : G) ^ 2 ^ m * dD.uv
      = dD.uv⁻¹ * (dD.u⁻¹ * (dD.a : G) ^ 2 ^ m * dD.u) * dD.uv := by rw [hswap]
    _ = (dD.uv⁻¹ * dD.u⁻¹) * (dD.a : G) ^ 2 ^ m * (dD.u * dD.uv) := by group
    _ = (dD.u⁻¹ * dD.uv⁻¹) * (dD.a : G) ^ 2 ^ m * (dD.uv * dD.u) := by
          rw [h1, dD.uv_comm_u]
    _ = dD.u⁻¹ * (dD.uv⁻¹ * (dD.a : G) ^ 2 ^ m * dD.uv) * dD.u := by group
    _ = dD.u⁻¹ * (dD.a : G) ^ 2 ^ m * dD.u := by rw [hfixa]
    _ = (dD.b : G) ^ 2 ^ m := hswap

theorem t121_φuv_ab_half {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t121 m hm).action.φuv
        ((2 ^ (m - 1) : ℕ) •
          (Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
            Torus.b (k := (StrothTypeIndex.t121 m hm).k))) =
      -((2 ^ (m - 1) : ℕ) •
          (Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
            Torus.b (k := (StrothTypeIndex.t121 m hm).k))) := by
  obtain ⟨v, hv⟩ := t121_uv_preimage (m := m) hm
  have hsq := (StrothTypeIndex.t121 m hm).action.rels.uv_sq
  have hvv : (StrothTypeIndex.t121 m hm).action.φuv
      ((StrothTypeIndex.t121 m hm).action.φuv v) = v := by
    have := DFunLike.congr_fun hsq v
    simpa using this
  have h2 : (StrothTypeIndex.t121 m hm).action.φuv
      ((StrothTypeIndex.t121 m hm).action.φuv v - v) =
      -((StrothTypeIndex.t121 m hm).action.φuv v - v) := by
    rw [map_sub, hvv]
    abel
  rwa [hv] at h2


theorem t121_d2_ofTorus {D : Subgroup G} {m : ℕ} {hm : 3 ≤ m}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t121 m hm)} :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 1) =
      dD.ofTorus ((2 ^ (m - 1) : ℕ) •
        (Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
          Torus.b (k := (StrothTypeIndex.t121 m hm).k))) := by
  rw [show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t121 m hm).k)) from dD.a_eq,
    show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t121 m hm).k)) from dD.b_eq,
    ← dD.ofTorus_add, ← dD.ofTorus_nsmul]

theorem t121_d2_sq_eq {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t121 m hm)} (h : F.IsD D dD) :
    (((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 1)) *
        (((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 1)) =
      ((F.dA.a : G)⁻¹) ^ 2 * ((F.dA.b : G)⁻¹) ^ 2 := by
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
      ((2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t121 m hm).k)) := by
    rw [hah, show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t121 m hm).k)) from dD.a_eq, ← dD.ofTorus_nsmul]
  have hbh_ofT : bh = dD.ofTorus
      ((2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t121 m hm).k)) := by
    rw [hbh, show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t121 m hm).k)) from dD.b_eq, ← dD.ofTorus_nsmul]
  have huv_ah : dD.uv⁻¹ * ah * dD.uv = ah := by
    simpa [hah] using t121_uv_fixes_a_half (dD := dD) (m := m) (hm := hm)
  have huv_bh : dD.uv⁻¹ * bh * dD.uv = bh := by
    simpa [hbh] using t121_uv_fixes_b_half (dD := dD) (m := m) (hm := hm)
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
    simpa [hah, hbh] using t121_u_swaps_a_half (dD := dD) (m := m) (hm := hm)
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
  have hua_ne : (2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t121 m hm).k) ≠
      (2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t121 m hm).k) := by
    intro htor
    have h1 := congrFun htor 1
    simp [Torus.a, Torus.b, gen, Pi.single_apply, nsmul_eq_mul] at h1
    have h1' : ((2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) = 0 := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact h1
    exact two_pow_pred_ne_zero (n := m + 1) (by omega) (by simpa using h1')
  have hahb_ne : ah ≠ bh := by
    intro heq
    have htor : (2 ^ m : ℕ) • Torus.a (k := (StrothTypeIndex.t121 m hm).k) =
        (2 ^ m : ℕ) • Torus.b (k := (StrothTypeIndex.t121 m hm).k) := by
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


theorem t121_d2_mem_A {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t121 m hm)} (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 1) ∈ F.A := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 1)
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
    have hxy_comm : x * y = y * x := mul_comm_mem_of_isMulCommutative (D := F.A) hxA hyA
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy_comm]
      _ = (x * x) * (y * y) := by group
      _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]
  have hd2sq : d2 * d2 = x ^ 2 * y ^ 2 := by
    simpa [d2, x, y] using t121_d2_sq_eq (m := m) (dD := dD) hm h
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

theorem t121_d2_eq_xy {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t121 m hm)} (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 1) =
        F.dA.toConfig.x * F.dA.toConfig.y ∨
      ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 1) =
        (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 1)
  let w : Torus (StrothTypeIndex.t121 m hm).k :=
    (2 ^ (m - 1) : ℕ) • (Torus.a + Torus.b)
  change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
    d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹
  have hd2A : d2 ∈ F.A := by
    simpa [d2] using t121_d2_mem_A (m := m) (dD := dD) hm h
  have hd2D : d2 ∈ D := by
    dsimp only [d2]
    exact D.pow_mem (D.mul_mem dD.a.2 dD.b.2) _
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t121_d2_ofTorus (m := m) (dD := dD)
  have hφu : (StrothTypeIndex.t121 m hm).action.φu w = w := by
    dsimp only [w]
    exact t121_u_fixes_ab_half_torus (m := m) hm
  have hφuv : (StrothTypeIndex.t121 m hm).action.φuv w = -w := by
    dsimp only [w]
    exact t121_φuv_ab_half (m := m) hm
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
      simpa [d2] using t121_d2_sq_eq (m := m) (dD := dD) hm h
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

theorem t121_isConj_uv_xyuv {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t121 m hm)} (h : F.IsD D dD) :
    IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv) := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 1)
  let w : Torus (StrothTypeIndex.t121 m hm).k :=
    (2 ^ (m - 1) : ℕ) • (Torus.a + Torus.b)
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t121_d2_ofTorus (m := m) (dD := dD)
  have hd2 : d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
    have h := t121_d2_eq_xy (m := m) (dD := dD) hm h
    change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ at h
    exact h
  obtain ⟨v, hv⟩ := t121_uv_preimage (m := m) hm
  have hφ : dD.ofTorus ((StrothTypeIndex.t121 m hm).action.φuv v - v) = d2 := by
    rw [hv]
    rw [hd2_ofT]
  exact isConj_uv_xyuv_of_d2 (τ := StrothTypeIndex.t121 m hm) h hd2 hφ


end StrothFrame.IsD

end CFSG.CGT.Stroth77
