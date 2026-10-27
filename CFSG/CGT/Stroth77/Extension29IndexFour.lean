module

public import CFSG.CGT.Stroth77.Extension212Group4
public import CFSG.CGT.Stroth77.Extension212Profile
public import CFSG.CGT.Stroth77.Extension29IndexTwo

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

section Base

theorem type111_rho_apply_gens (t : ℕ) (i j l : ℤ) :
    (Type111.action t).φρ (i • gen (Type111.k t) 0 + j • gen (Type111.k t) 1 +
        l • gen (Type111.k t) 2) =
      (i - 2 * l) • gen (Type111.k t) 0 + (-l) • gen (Type111.k t) 1 +
        (j - l) • gen (Type111.k t) 2 := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
  have hc := Type111.rho_c t
  have ha := Type111.rho_a t
  have hb := Type111.rho_b t
  simp only [Torus.c, Torus.a, Torus.b] at hc ha hb
  rw [hc, ha, hb]
  module

theorem type111_t_apply_gens (t : ℕ) (i j l : ℤ) :
    (Type111.action t).φt (i • gen (Type111.k t) 0 + j • gen (Type111.k t) 1 +
        l • gen (Type111.k t) 2) =
      (i + (-8 * 2 ^ t - 2) * l) • gen (Type111.k t) 0 +
        (2 * i + (4 * 2 ^ t - 1) * j + (-4 * 2 ^ t - 2) * l) • gen (Type111.k t) 1 +
        (4 * 2 ^ t * i + (-4 * 2 ^ t - 1) * l) • gen (Type111.k t) 2 := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
  have hc := Type111.t_c t
  have ha := Type111.t_a t
  have hb := Type111.t_b t
  simp only [Torus.c, Torus.a, Torus.b] at hc ha hb
  rw [hc, ha, hb]
  module

theorem dvd_of_dvd_three_mul_Idx4R {e : ℕ} {l : ℤ} (h : (2 : ℤ) ^ e ∣ 3 * l) :
    (2 : ℤ) ^ e ∣ l := by
  have hcop : IsCoprime ((2 : ℤ) ^ e) 3 := by
    have : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact this.pow_left
  exact hcop.dvd_of_dvd_mul_left h

theorem t111_fixed_rho_t (t : ℕ) (y : Torus (Type111.k t))
    (hρ : (Type111.action t).φρ y = y) (ht : (Type111.action t).φt y = y) : y = 0 := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type111.k t) y
  have hρ' := hρ
  rw [type111_rho_apply_gens] at hρ'
  have ht' := ht
  rw [type111_t_apply_gens] at ht'
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ'
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht'
  change (2 : ℤ) ^ (t + 3) ∣ _ at hρ1 hρ2 ht1
  have hl : (2 : ℤ) ^ (t + 3) ∣ l := by
    apply dvd_of_dvd_three_mul_Idx4R
    have h := dvd_add hρ1 hρ2
    convert h using 1
    ring
  have hj : (2 : ℤ) ^ (t + 3) ∣ j := by
    have h := dvd_sub hρ1 hl
    convert h using 1
    ring
  obtain ⟨a, ha⟩ := ht1
  obtain ⟨b, hb⟩ := hj
  obtain ⟨c, hc⟩ := hl
  have hi : i = 2 ^ (t + 2) * (-(a + (4 * 2 ^ t - 2) * b - (4 * 2 ^ t + 2) * c)) := by
    have h2 : (2 : ℤ) * i = 2 * (2 ^ (t + 2) * (-(a + (4 * 2 ^ t - 2) * b -
        (4 * 2 ^ t + 2) * c))) := by
      rw [hb, hc] at ha
      linear_combination (-1 : ℤ) * ha
    exact mul_left_cancel₀ (by norm_num) h2
  rw [hi, hb, hc]
  apply (zsmul_gens_eq_of_dvd (p' := 0) (q' := 0) (r' := 0) ?_ ?_ ?_).trans (by module)
  · change (2 : ℤ) ^ (t + 2) ∣ _
    exact ⟨a + (4 * 2 ^ t - 2) * b - (4 * 2 ^ t + 2) * c, by ring⟩
  · change (2 : ℤ) ^ (t + 3) ∣ _
    exact ⟨-b, by ring⟩
  · change (2 : ℤ) ^ (t + 3) ∣ _
    exact ⟨-c, by ring⟩

theorem fix4_t111 (t : ℕ) (y : Torus (Type111.k t))
    (hρ : ∃ z : Torus (Type111.k t), 4 • z = (Type111.action t).φρ y - y)
    (ht : ∃ z : Torus (Type111.k t), 4 • z = (Type111.action t).φt y - y) :
    ∃ z : Torus (Type111.k t), 2 • z = y := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type111.k t) y
  obtain ⟨zρ, hzρ⟩ := hρ
  obtain ⟨zt, hzt⟩ := ht
  obtain ⟨a0, a1, a2, rfl⟩ := torus_eq_zsmul_gens (Type111.k t) zρ
  obtain ⟨b0, b1, b2, rfl⟩ := torus_eq_zsmul_gens (Type111.k t) zt
  rw [type111_rho_apply_gens, nsmul_zsmul_gens] at hzρ
  rw [type111_t_apply_gens, nsmul_zsmul_gens] at hzt
  have eρ : (i - 2 * l) • gen (Type111.k t) 0 + (-l) • gen (Type111.k t) 1 +
        (j - l) • gen (Type111.k t) 2 -
      (i • gen (Type111.k t) 0 + j • gen (Type111.k t) 1 + l • gen (Type111.k t) 2) =
      (-2 * l) • gen (Type111.k t) 0 + (-l - j) • gen (Type111.k t) 1 +
        (j - 2 * l) • gen (Type111.k t) 2 := by
    module
  have et : (i + (-8 * 2 ^ t - 2) * l) • gen (Type111.k t) 0 +
        (2 * i + (4 * 2 ^ t - 1) * j + (-4 * 2 ^ t - 2) * l) • gen (Type111.k t) 1 +
        (4 * 2 ^ t * i + (-4 * 2 ^ t - 1) * l) • gen (Type111.k t) 2 -
      (i • gen (Type111.k t) 0 + j • gen (Type111.k t) 1 + l • gen (Type111.k t) 2) =
      ((-8 * 2 ^ t - 2) * l) • gen (Type111.k t) 0 +
        (2 * i + (4 * 2 ^ t - 2) * j + (-4 * 2 ^ t - 2) * l) • gen (Type111.k t) 1 +
        (4 * 2 ^ t * i + (-4 * 2 ^ t - 2) * l) • gen (Type111.k t) 2 := by
    module
  rw [eρ] at hzρ
  rw [et] at hzt
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hzρ
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq hzt
  change (2 : ℤ) ^ (t + 3) ∣ _ at hρ1 hρ2 ht1
  have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ (t + 3) := ⟨2 ^ (t + 1), by ring⟩
  obtain ⟨u1, hu1⟩ := h4.trans hρ1
  obtain ⟨u2, hu2⟩ := h4.trans hρ2
  obtain ⟨v1, hv1⟩ := h4.trans ht1
  push_cast at hu1 hu2 hv1
  have hl : 4 ∣ l := by omega
  have hj : 4 ∣ j := by omega
  obtain ⟨l', rfl⟩ := hl
  obtain ⟨j', rfl⟩ := hj
  ring_nf at hv1
  obtain ⟨i', rfl⟩ : 2 ∣ i := by omega
  refine ⟨i' • gen (Type111.k t) 0 + (2 * j') • gen (Type111.k t) 1 +
    (2 * l') • gen (Type111.k t) 2, ?_⟩
  rw [two_nsmul]
  module

theorem rhoPar_t111 {t : ℕ} (hk : ∀ i, 1 ≤ Type111.k t i) (y : Torus (Type111.k t)) :
    parityTorus _ hk ((Type111.action t).φρ y) = rhoBar300 (parityTorus _ hk y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type111.k t) y
  rw [type111_rho_apply_gens, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r
  · simp [rhoBar300, h2]
  · simp [rhoBar300, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar300, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

end Base

section Target

variable (t : ℕ) (hm : 2 ≤ t + 2)

section Matrices

theorem t210_uv_eq : (StrothTypeIndex.t210 (t + 2) hm).action.uv = Type210.uvM (t + 2) := rfl
theorem t210_t_eq : (StrothTypeIndex.t210 (t + 2) hm).action.t = Type210.tM (t + 2) := rfl
theorem t210_u_eq : (StrothTypeIndex.t210 (t + 2) hm).action.u = Type210.uM (t + 2) := rfl
theorem t210_ρ_eq : (StrothTypeIndex.t210 (t + 2) hm).action.ρ = Type210.ρM := rfl
theorem t211_uv_eq : (StrothTypeIndex.t211 (t + 2) hm).action.uv = Type211.uvM (t + 2) := rfl
theorem t211_t_eq : (StrothTypeIndex.t211 (t + 2) hm).action.t = Type211.tM (t + 2) := rfl
theorem t211_u_eq : (StrothTypeIndex.t211 (t + 2) hm).action.u = Type211.uM (t + 2) := rfl
theorem t211_ρ_eq : (StrothTypeIndex.t211 (t + 2) hm).action.ρ = Type211.ρM := rfl
theorem t111_uv_eq : (StrothTypeIndex.t111 t).action.uv = Type111.uvM t := rfl
theorem t111_t_eq : (StrothTypeIndex.t111 t).action.t = Type111.tM t := rfl
theorem t111_u_eq : (StrothTypeIndex.t111 t).action.u = Type111.uM t := rfl
theorem t111_ρ_eq : (StrothTypeIndex.t111 t).action.ρ = Type111.ρM t := rfl

end Matrices

theorem profile4_t210 :
    Profile4 (StrothTypeIndex.t210 (t + 2) hm).k (StrothTypeIndex.t210 (t + 2) hm).action.φuv
      (StrothTypeIndex.t210 (t + 2) hm).action.φt (StrothTypeIndex.t210 (t + 2) hm).action.φu
      (StrothTypeIndex.t210 (t + 2) hm).action.φρ := by
  refine profile4_of_par (k := t + 2) (n := t + 4) rfl (by omega) (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  all_goals simp only [t210_uv_eq, t210_t_eq, t210_u_eq, t210_ρ_eq,
    show t + 4 - (t + 2) = 2 by omega]
  · refine ⟨⟨-2, ?_⟩, ⟨4 * 2 ^ t, ?_⟩, ⟨-2 * 2 ^ t + 1, ?_⟩,
      ⟨-16 * (2 ^ t) ^ 2 - 22 * 2 ^ t + 1, ?_⟩, ⟨-40 * (2 ^ t) ^ 2 - 16 * 2 ^ t, ?_⟩⟩ <;>
    simp [Type210.uvM, Type210.uvA, Type210.tM, Type210.ρM, ofCols_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three] <;> ring
  · refine ⟨⟨0, ?_⟩, ⟨-2 * 2 ^ t - 1, ?_⟩, ⟨4 * 2 ^ t, ?_⟩, ⟨2 * 2 ^ t - 1, ?_⟩,
      ⟨6 * 2 ^ t - 1, ?_⟩⟩ <;>
    simp [Type210.tM, Type210.uvA, Type210.ρM, ofCols_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring
  · refine ⟨⟨2 ^ t, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
    simp [Type210.uM, uMat, ofCols_apply] <;> ring
  · refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨-1, ?_⟩, ⟨-1, ?_⟩⟩ <;>
    simp [Type210.ρM, ofCols_apply]
  · refine ⟨2 * 2 ^ t - 1, -1, ?_, ?_, ⟨2 ^ t - 1, ?_⟩, ⟨-1, ?_⟩⟩ <;>
    (try simp [Type210.uvM, ofCols_apply]) <;> ring
  · refine ⟨1, 2 * 2 ^ t, ?_, ?_, ⟨0, ?_⟩, ⟨2 ^ t, ?_⟩⟩ <;>
    (try simp [Type210.tM, ofCols_apply]) <;> ring
  · exact ⟨0, 0, by simp [Type210.uM, uMat, ofCols_apply],
      by simp [Type210.uM, uMat, ofCols_apply], by decide, by decide⟩
  · exact ⟨0, 0, by simp [Type210.ρM, ofCols_apply], by simp [Type210.ρM, ofCols_apply],
      by decide, by decide⟩

theorem twist4_t210 :
    Twist4 (StrothTypeIndex.t210 (t + 2) hm).k (StrothTypeIndex.t210 (t + 2) hm).action.φuv
      (StrothTypeIndex.t210 (t + 2) hm).action.φt (StrothTypeIndex.t210 (t + 2) hm).action.φu
      (StrothTypeIndex.t210 (t + 2) hm).action.φρ (StrothTypeIndex.t211 (t + 2) hm).action.φuv
      (StrothTypeIndex.t211 (t + 2) hm).action.φt (StrothTypeIndex.t211 (t + 2) hm).action.φu
      (StrothTypeIndex.t211 (t + 2) hm).action.φρ := by
  have hK0 : (StrothTypeIndex.t210 (t + 2) hm).k 0 = t + 2 := rfl
  have hK1 : (StrothTypeIndex.t210 (t + 2) hm).k 1 = t + 4 := rfl
  have hK2 : (StrothTypeIndex.t210 (t + 2) hm).k 2 = t + 4 := rfl
  have hK0' : (StrothTypeIndex.t211 (t + 2) hm).k 0 = t + 2 := rfl
  have hK1' : (StrothTypeIndex.t211 (t + 2) hm).k 1 = t + 4 := rfl
  have hK2' : (StrothTypeIndex.t211 (t + 2) hm).k 2 = t + 4 := rfl
  have s0 : t + 2 - 1 = t + 1 := by omega
  have s1 : t + 4 - 1 = t + 3 := by omega
  have e0 {M M' : IntMat} (hM : Compat (StrothTypeIndex.t210 (t + 2) hm).k M)
      (hM' : Compat (StrothTypeIndex.t210 (t + 2) hm).k M') (j : Fin 3)
      (h0 : M 0 j = M' 0 j) (h1 : M 1 j = M' 1 j) (h2 : M 2 j = M' 2 j) :
      matAct _ M' hM' (gen _ j) = matAct _ M hM (gen _ j) := by
    rw [matAct_gen_eq, matAct_gen_eq, h0, h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e0 _ _ 0 (by simp [t210_uv_eq, t211_uv_eq, Type210.uvM, Type211.uvM, ofCols_apply])
      (by simp [t210_uv_eq, t211_uv_eq, Type210.uvM, Type211.uvM, ofCols_apply])
      (by simp [t210_uv_eq, t211_uv_eq, Type210.uvM, Type211.uvM, ofCols_apply])
  · refine matAct_gen_eq_add_tw _ _ 1 0 0 1 ?_ ?_ ?_ <;>
      simp only [hK0, hK1, hK2, hK0', hK1', hK2', s0, s1, t210_uv_eq, t211_uv_eq]
    · exact ⟨0, by simp [Type210.uvM, Type211.uvM, Type210.uvA, Type211.uvA, ofCols_apply]⟩
    · exact ⟨0, by simp [Type210.uvM, Type211.uvM, Type210.uvA, Type211.uvA, ofCols_apply]⟩
    · exact ⟨0, by
        simp [Type210.uvM, Type211.uvM, Type210.uvA, Type211.uvA, ofCols_apply]
        ring⟩
  · refine matAct_gen_eq_add_tw _ _ 2 0 1 0 ?_ ?_ ?_ <;>
      simp only [hK0, hK1, hK2, hK0', hK1', hK2', s0, s1, t210_uv_eq, t211_uv_eq]
    · exact ⟨12 * 2 ^ t, by
        simp [Type210.uvM, Type211.uvM, Type210.uvA, Type211.uvA, Type210.tM, Type211.tM,
          Type210.ρM, Type211.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨4 * 2 ^ t - 1, by
        simp [Type210.uvM, Type211.uvM, Type210.uvA, Type211.uvA, Type210.tM, Type211.tM,
          Type210.ρM, Type211.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨0, by
        simp [Type210.uvM, Type211.uvM, Type210.uvA, Type211.uvA, Type210.tM, Type211.tM,
          Type210.ρM, Type211.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
  · exact e0 _ _ 0 (by simp [t210_t_eq, t211_t_eq, Type210.tM, Type211.tM, ofCols_apply])
      (by simp [t210_t_eq, t211_t_eq, Type210.tM, Type211.tM, ofCols_apply])
      (by simp [t210_t_eq, t211_t_eq, Type210.tM, Type211.tM, ofCols_apply])
  · refine matAct_gen_eq_add_tw _ _ 1 0 1 0 ?_ ?_ ?_ <;>
      simp only [hK0, hK1, hK2, hK0', hK1', hK2', s0, s1, t210_t_eq, t211_t_eq]
    · exact ⟨0, by simp [Type210.tM, Type211.tM, ofCols_apply]⟩
    · exact ⟨0, by
        simp [Type210.tM, Type211.tM, ofCols_apply]
        ring⟩
    · exact ⟨0, by simp [Type210.tM, Type211.tM, ofCols_apply]⟩
  · refine matAct_gen_eq_add_tw _ _ 2 0 1 1 ?_ ?_ ?_ <;>
      simp only [hK0, hK1, hK2, hK0', hK1', hK2', s0, s1, t210_t_eq, t211_t_eq]
    · exact ⟨2, by
        simp [Type210.tM, Type211.tM, Type210.uvA, Type211.uvA, Type210.ρM, Type211.ρM,
          ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨1, by
        simp [Type210.tM, Type211.tM, Type210.uvA, Type211.uvA, Type210.ρM, Type211.ρM,
          ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨1, by
        simp [Type210.tM, Type211.tM, Type210.uvA, Type211.uvA, Type210.ρM, Type211.ρM,
          ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
  · exact e0 _ _ 0 (by simp [t210_u_eq, t211_u_eq, Type210.uM, Type211.uM, uMat, ofCols_apply])
      (by simp [t210_u_eq, t211_u_eq, Type210.uM, Type211.uM, uMat, ofCols_apply])
      (by simp [t210_u_eq, t211_u_eq, Type210.uM, Type211.uM, uMat, ofCols_apply])
  · exact e0 _ _ 1 (by simp [t210_u_eq, t211_u_eq, Type210.uM, Type211.uM, uMat, ofCols_apply])
      (by simp [t210_u_eq, t211_u_eq, Type210.uM, Type211.uM, uMat, ofCols_apply])
      (by simp [t210_u_eq, t211_u_eq, Type210.uM, Type211.uM, uMat, ofCols_apply])
  · exact e0 _ _ 2 (by simp [t210_u_eq, t211_u_eq, Type210.uM, Type211.uM, uMat, ofCols_apply])
      (by simp [t210_u_eq, t211_u_eq, Type210.uM, Type211.uM, uMat, ofCols_apply])
      (by simp [t210_u_eq, t211_u_eq, Type210.uM, Type211.uM, uMat, ofCols_apply])
  · exact e0 _ _ 0 (by simp [t210_ρ_eq, t211_ρ_eq, Type210.ρM, Type211.ρM, ofCols_apply])
      (by simp [t210_ρ_eq, t211_ρ_eq, Type210.ρM, Type211.ρM, ofCols_apply])
      (by simp [t210_ρ_eq, t211_ρ_eq, Type210.ρM, Type211.ρM, ofCols_apply])
  · exact e0 _ _ 1 (by simp [t210_ρ_eq, t211_ρ_eq, Type210.ρM, Type211.ρM, ofCols_apply])
      (by simp [t210_ρ_eq, t211_ρ_eq, Type210.ρM, Type211.ρM, ofCols_apply])
      (by simp [t210_ρ_eq, t211_ρ_eq, Type210.ρM, Type211.ρM, ofCols_apply])
  · exact e0 _ _ 2 (by simp [t210_ρ_eq, t211_ρ_eq, Type210.ρM, Type211.ρM, ofCols_apply])
      (by simp [t210_ρ_eq, t211_ρ_eq, Type210.ρM, Type211.ρM, ofCols_apply])
      (by simp [t210_ρ_eq, t211_ρ_eq, Type210.ρM, Type211.ρM, ofCols_apply])

theorem restrict_t111_t210 :
    MatEq (StrothTypeIndex.t210 (t + 2) hm).k
        ((StrothTypeIndex.t210 (t + 2) hm).action.uv * diag4)
        (diag4 * (StrothTypeIndex.t111 t).action.uv) ∧
      MatEq (StrothTypeIndex.t210 (t + 2) hm).k
        ((StrothTypeIndex.t210 (t + 2) hm).action.t * diag4)
        (diag4 * (StrothTypeIndex.t111 t).action.t) ∧
      MatEq (StrothTypeIndex.t210 (t + 2) hm).k
        ((StrothTypeIndex.t210 (t + 2) hm).action.u * diag4)
        (diag4 * (StrothTypeIndex.t111 t).action.u) ∧
      MatEq (StrothTypeIndex.t210 (t + 2) hm).k
        ((StrothTypeIndex.t210 (t + 2) hm).action.ρ * diag4)
        (diag4 * (StrothTypeIndex.t111 t).action.ρ) := by
  rw [t210_uv_eq, t210_t_eq, t210_u_eq, t210_ρ_eq, t111_uv_eq, t111_t_eq, t111_u_eq, t111_ρ_eq]
  refine ⟨MatEq.of_witness (W := !![0, 1, -20 * 2 ^ t - 8; 0, 1, -6 * 2 ^ t - 6;
      0, -1, -10 * 2 ^ t - 3]) ?_,
    MatEq.of_witness (W := !![0, 1, 5; 0, -1, 1; 0, 1, 2]) ?_,
    MatEq.of_witness (W := !![0, 1, -2 * 2 ^ t - 1; 0, 0, 0; 0, 0, 0]) ?_,
    MatEq.of_eq ?_⟩
  · intro r c
    fin_cases r <;> fin_cases c <;>
      simp [StrothTypeIndex.k, Type210.k, diag4, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Type210.uvM, Type210.uvA, Type210.tM, Type210.ρM, Type111.uvM, Type111.uvA, Type111.tM,
        Type111.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, pow_add,
        -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
      ring1
  · intro r c
    fin_cases r <;> fin_cases c <;>
      simp [StrothTypeIndex.k, Type210.k, diag4, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Type210.uvA, Type210.tM, Type210.ρM, Type111.uvA, Type111.tM, Type111.ρM, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three, pow_add, -mul_eq_zero,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
      ring1
  · intro r c
    fin_cases r <;> fin_cases c <;>
      simp [StrothTypeIndex.k, Type210.k, diag4, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Type210.uM, Type111.uM, uMat, ofCols_apply, pow_add, -mul_eq_zero,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
      ring1
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [diag4, Matrix.mul_diagonal, Matrix.diagonal_mul, Type210.ρM, Type111.ρM, ofCols_apply]

end Target

theorem hasStrothType_t210_or_t211_of_data_t111 {t : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t111 t)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothType C (StrothTypeIndex.t210 (t + 2) (by omega)) ∨
      HasStrothType C (StrothTypeIndex.t211 (t + 2) (by omega)) := by
  have hm : 2 ≤ t + 2 := by omega
  obtain ⟨cV, cW, cU, cR⟩ := restrict_t111_t210 t hm
  rcases hasStrothType_or_of_index_four_of_data D hBC hC hrel hL hH hcS (hk_t111 t)
      (rhoPar_t111 (hk_t111 t)) (rho_gens_t111 t).2.1 (t111_fixed_rho_t t) (fix4_t111 t)
      (StrothTypeIndex.t210 (t + 2) hm) rfl rfl rfl (StrothTypeIndex.t211 (t + 2) hm).action
      (profile4_t210 t hm) (twist4_t210 t hm) cV cW cU cR with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothType_of_basisChange D hL (StrothTypeIndex.t211 (t + 2) hm) E φ h2)

theorem hasStrothTypeOver_t210_or_t211_of_data_t111 {t : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t111 t)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t210 (t + 2) (by omega)) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t211 (t + 2) (by omega)) := by
  have hm : 2 ≤ t + 2 := by omega
  obtain ⟨cV, cW, cU, cR⟩ := restrict_t111_t210 t hm
  rcases hasStrothTypeOver_or_of_index_four_of_data D hBC hC hrel hL hH hcS (hk_t111 t)
      (rhoPar_t111 (hk_t111 t)) (rho_gens_t111 t).2.1 (t111_fixed_rho_t t) (fix4_t111 t)
      (StrothTypeIndex.t210 (t + 2) hm) rfl rfl rfl (StrothTypeIndex.t211 (t + 2) hm).action
      (profile4_t210 t hm) (twist4_t210 t hm) cV cW cU cR with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothTypeOver_of_basisChange D hL (StrothTypeIndex.t211 (t + 2) hm) E φ h2)

end CFSG.CGT.Stroth77
