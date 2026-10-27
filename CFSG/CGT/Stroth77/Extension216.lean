module

public import CFSG.CGT.Stroth77.Extension212Group4
public import CFSG.CGT.Stroth77.Extension212Profile
public import CFSG.CGT.Stroth77.Extension216Base

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem sq_of_fixed_mod_two_t330 {m : ℕ} (hm : 3 ≤ m) (v : Torus (StrothTypeIndex.t330 m hm).k)
    (hρ : ∃ z, 2 • z = (StrothTypeIndex.t330 m hm).action.φρ v - v)
    (ht : ∃ z, 2 • z = (StrothTypeIndex.t330 m hm).action.φt v - v) : ∃ z, 2 • z = v := by
  have hρ0 := (parityTorus_eq_zero_iff (t330_k_pos hm) _).mpr hρ
  have ht0 := (parityTorus_eq_zero_iff (t330_k_pos hm) _).mpr ht
  rw [map_sub, parityTorus_rho_t330] at hρ0
  rw [map_sub, parityTorus_t_t330] at ht0
  exact (parityTorus_eq_zero_iff (t330_k_pos hm) v).mp
    (fixed_check_t330 _ (sub_eq_zero.mp hρ0) (sub_eq_zero.mp ht0))

theorem false_of_index_two_of_data_t330 {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t330 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    False :=
  false_of_index_two_of_data D hBC hC hrel hL hH hcS
    (fun v _ ht _ hρ => sq_of_fixed_mod_two_t330 hm v hρ ht)

theorem restrict_t330_t130 {m : ℕ} (hm : 3 ≤ m) :
    MatEq (StrothTypeIndex.t130 m hm).k ((StrothTypeIndex.t130 m hm).action.uv * diag4)
        (diag4 * (StrothTypeIndex.t330 m hm).action.uv) ∧
      MatEq (StrothTypeIndex.t130 m hm).k ((StrothTypeIndex.t130 m hm).action.t * diag4)
        (diag4 * (StrothTypeIndex.t330 m hm).action.t) ∧
      MatEq (StrothTypeIndex.t130 m hm).k ((StrothTypeIndex.t130 m hm).action.u * diag4)
        (diag4 * (StrothTypeIndex.t330 m hm).action.u) ∧
      MatEq (StrothTypeIndex.t130 m hm).k ((StrothTypeIndex.t130 m hm).action.ρ * diag4)
        (diag4 * (StrothTypeIndex.t330 m hm).action.ρ) :=
  ⟨t330_dbl_t130_uvM (Type32x.data m (by omega)) (Type130.data m (by omega)),
    t330_dbl_t130_tM (Type32x.data m (by omega)) (Type130.data m (by omega)),
    t330_dbl_t130_uM (Type32x.data m (by omega)) (Type130.data m (by omega)),
    t330_dbl_t130_ρM (Type32x.data m (by omega)) (Type130.data m (by omega))⟩

theorem profile4_t130 {m : ℕ} (hm : 3 ≤ m) :
    Profile4 (StrothTypeIndex.t130 m hm).k (StrothTypeIndex.t130 m hm).action.φuv
      (StrothTypeIndex.t130 m hm).action.φt (StrothTypeIndex.t130 m hm).action.φu
      (StrothTypeIndex.t130 m hm).action.φρ := by
  have hi := iV_cast_two (m + 1)
  have hF := FV_cast_two (n := m + 1) (by omega)
  have hG := GV_cast_two (n := m + 1) (by omega)
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hN : (2 : ZMod 2) ^ m = 0 := by rw [h2]; exact zero_pow (by omega)
  have hK : (2 : ZMod 2) ^ (m - 1) = 0 := by rw [h2]; exact zero_pow (by omega)
  have e2m : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hKe : Even ((2 : ℤ) ^ (m - 1)) := Int.even_pow.mpr ⟨even_two, by omega⟩
  have euv : (StrothTypeIndex.t130 m hm).action.uv = Type130.uvM (Type120.iV (m + 1))
      (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) := rfl
  have et : (StrothTypeIndex.t130 m hm).action.t = Type130.tM (Type120.iV (m + 1))
      (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) := rfl
  have eu : (StrothTypeIndex.t130 m hm).action.u =
      Type130.uM (Type120.FV (m + 1)) (2 ^ (m - 1)) := rfl
  have eρ : (StrothTypeIndex.t130 m hm).action.ρ = Type130.ρM := rfl
  refine profile4_of_par (k := m) (n := m + 1) rfl (by omega) le_rfl _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [euv]
    refine ⟨odd_of_cast_two ?_, odd_of_cast_two ?_, even_of_cast_two ?_, even_of_cast_two ?_,
      odd_of_cast_two ?_⟩ <;>
    simp [Type130.uvM, Type130.uvA, Type130.tM, Type130.ρM, ofCols_mulVec, ofCols_apply, hi, hF,
      hG, hN] <;> decide
  · rw [et]
    refine ⟨odd_of_cast_two ?_, odd_of_cast_two ?_, even_of_cast_two ?_, even_of_cast_two ?_,
      odd_of_cast_two ?_⟩ <;>
    simp [Type130.tM, Type130.uvA, Type130.ρM, ofCols_mulVec, ofCols_apply, hi, hF, hG,
      hN] <;> decide
  · rw [eu]
    refine ⟨odd_of_cast_two ?_, even_of_cast_two ?_, odd_of_cast_two ?_, odd_of_cast_two ?_,
      even_of_cast_two ?_⟩ <;>
    simp [Type130.uM, uMat, ofCols_apply, hF, hK] <;> decide
  · rw [eρ]
    refine ⟨odd_of_cast_two ?_, even_of_cast_two ?_, odd_of_cast_two ?_, odd_of_cast_two ?_,
      odd_of_cast_two ?_⟩ <;>
    simp [Type130.ρM, ofCols_apply] <;> decide
  · rw [euv]
    refine ⟨1 + 2 ^ (m - 1), -1, ?_, ?_, hKe.one_add, ⟨-1, by norm_num⟩⟩
    · simp [Type130.uvM, ofCols_apply, e2m]
      ring
    · simp [Type130.uvM, ofCols_apply]
  · rw [et]
    refine ⟨1, 2 + 2 ^ (m - 1), ?_, ?_, odd_one, ?_⟩
    · simp [Type130.tM, ofCols_apply]
    · simp [Type130.tM, ofCols_apply, e2m]
      ring
    · exact even_two.add hKe
  · rw [eu]
    refine ⟨0, 0, ?_, ?_, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩ <;>
      simp [Type130.uM, uMat, ofCols_apply]
  · rw [eρ]
    refine ⟨0, 0, ?_, ?_, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩ <;>
      simp [Type130.ρM, ofCols_apply]

theorem twist_data_t130 {m : ℕ} (hm : 2 ≤ m) {i F G N K J : ℤ}
    (h : Type130.Data m i F G N K J) :
    i = 8 * G + 19 ∧ F = 4 * G + 9 ∧ N = 4 * J ∧ K = 2 * J ∧ (2 : ℤ) ^ m = 4 * J ∧
      (2 : ℤ) ^ (m - 1) = 2 * J ∧ (2 : ℤ) ^ (m + 1) = 8 * J := by
  obtain ⟨hi, hF, hN, hK, hJ, -⟩ := h
  have e : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have h1 : 2 * (2 : ℤ) ^ (m - 1) = 2 * (2 * J) := by rw [← e, ← hN, hK, hJ]
  refine ⟨hi, hF, by rw [hK, hJ]; ring, hJ, by rw [← hN, hK, hJ]; ring, by linarith,
    by rw [pow_succ, ← hN, hK, hJ]; ring⟩

theorem twist_uv_t130 {m : ℕ} (hm : 2 ≤ m) {i F G N K J : ℤ}
    (h : Type130.Data m i F G N K J) :
    ((2 : ℤ) ^ m ∣ (Type130.uvM i F G N 0 1 + 0 * 2 ^ (m - 1)) - Type131.uvM i F G N 0 1 ∧
      (2 : ℤ) ^ (m + 1) ∣ (Type130.uvM i F G N 1 1 + 0 * 2 ^ (m + 1 - 1)) -
        Type131.uvM i F G N 1 1 ∧
      (2 : ℤ) ^ (m + 1) ∣ (Type130.uvM i F G N 2 1 + 1 * 2 ^ (m + 1 - 1)) -
        Type131.uvM i F G N 2 1) ∧
    ((2 : ℤ) ^ m ∣ (Type130.uvM i F G N 0 2 + 0 * 2 ^ (m - 1)) - Type131.uvM i F G N 0 2 ∧
      (2 : ℤ) ^ (m + 1) ∣ (Type130.uvM i F G N 1 2 + 1 * 2 ^ (m + 1 - 1)) -
        Type131.uvM i F G N 1 2 ∧
      (2 : ℤ) ^ (m + 1) ∣ (Type130.uvM i F G N 2 2 + 0 * 2 ^ (m + 1 - 1)) -
        Type131.uvM i F G N 2 2) := by
  obtain ⟨rfl, rfl, rfl, rfl, h0, h1, h2⟩ := twist_data_t130 hm h
  have hs : m + 1 - 1 = m := rfl
  rw [hs, h0, h1, h2]
  refine ⟨⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩, ⟨-64 * G ^ 2 - 376 * G - 532, ?_⟩,
    ⟨-36 * G - 2 * J - 85, ?_⟩, ⟨0, ?_⟩⟩ <;>
  simp [Type130.uvM, Type131.uvM, Type130.uvA, Type131.uvA, Type130.tM, Type131.tM, Type130.ρM,
    Type131.ρM, ofCols_mulVec, ofCols_apply] <;> ring

theorem twist_t_t130 {m : ℕ} (hm : 2 ≤ m) {i F G N K J : ℤ}
    (h : Type130.Data m i F G N K J) :
    ((2 : ℤ) ^ m ∣ (Type130.tM i F G N 0 1 + 0 * 2 ^ (m - 1)) - Type131.tM i F G N 0 1 ∧
      (2 : ℤ) ^ (m + 1) ∣ (Type130.tM i F G N 1 1 + 1 * 2 ^ (m + 1 - 1)) -
        Type131.tM i F G N 1 1 ∧
      (2 : ℤ) ^ (m + 1) ∣ (Type130.tM i F G N 2 1 + 0 * 2 ^ (m + 1 - 1)) -
        Type131.tM i F G N 2 1) ∧
    ((2 : ℤ) ^ m ∣ (Type130.tM i F G N 0 2 + 0 * 2 ^ (m - 1)) - Type131.tM i F G N 0 2 ∧
      (2 : ℤ) ^ (m + 1) ∣ (Type130.tM i F G N 1 2 + 1 * 2 ^ (m + 1 - 1)) -
        Type131.tM i F G N 1 2 ∧
      (2 : ℤ) ^ (m + 1) ∣ (Type130.tM i F G N 2 2 + 1 * 2 ^ (m + 1 - 1)) -
        Type131.tM i F G N 2 2) := by
  obtain ⟨rfl, rfl, rfl, rfl, h0, h1, h2⟩ := twist_data_t130 hm h
  have hs : m + 1 - 1 = m := rfl
  rw [hs, h0, h1, h2]
  refine ⟨⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩, ⟨2, ?_⟩, ⟨1, ?_⟩, ⟨1, ?_⟩⟩ <;>
  simp [Type130.tM, Type131.tM, Type130.uvA, Type131.uvA, Type130.ρM, Type131.ρM,
    ofCols_mulVec, ofCols_apply] <;> ring

theorem twist4_t130 {m : ℕ} (hm : 3 ≤ m) :
    Twist4 (StrothTypeIndex.t130 m hm).k (StrothTypeIndex.t130 m hm).action.φuv
      (StrothTypeIndex.t130 m hm).action.φt (StrothTypeIndex.t130 m hm).action.φu
      (StrothTypeIndex.t130 m hm).action.φρ (StrothTypeIndex.t131 m hm).action.φuv
      (StrothTypeIndex.t131 m hm).action.φt (StrothTypeIndex.t131 m hm).action.φu
      (StrothTypeIndex.t131 m hm).action.φρ := by
  obtain ⟨⟨v10, v11, v12⟩, ⟨v20, v21, v22⟩⟩ := twist_uv_t130 (by omega) (Type130.data m (by omega))
  obtain ⟨⟨w10, w11, w12⟩, ⟨w20, w21, w22⟩⟩ := twist_t_t130 (by omega) (Type130.data m (by omega))
  have e0 {M M' : IntMat} (hM : Compat (StrothTypeIndex.t130 m hm).k M)
      (hM' : Compat (StrothTypeIndex.t130 m hm).k M') (j : Fin 3)
      (h0 : M 0 j = M' 0 j) (h1 : M 1 j = M' 1 j) (h2 : M 2 j = M' 2 j) :
      matAct _ M' hM' (gen _ j) = matAct _ M hM (gen _ j) := by
    rw [matAct_gen_eq, matAct_gen_eq, h0, h1, h2]
  have euv : (StrothTypeIndex.t130 m hm).action.uv = Type130.uvM (Type120.iV (m + 1))
      (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) := rfl
  have euv' : (StrothTypeIndex.t131 m hm).action.uv = Type131.uvM (Type120.iV (m + 1))
      (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) := rfl
  have et : (StrothTypeIndex.t130 m hm).action.t = Type130.tM (Type120.iV (m + 1))
      (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) := rfl
  have et' : (StrothTypeIndex.t131 m hm).action.t = Type131.tM (Type120.iV (m + 1))
      (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) := rfl
  have eu : (StrothTypeIndex.t130 m hm).action.u =
      Type130.uM (Type120.FV (m + 1)) (2 ^ (m - 1)) := rfl
  have eu' : (StrothTypeIndex.t131 m hm).action.u =
      Type131.uM (Type120.FV (m + 1)) (2 ^ (m - 1)) := rfl
  have eρ : (StrothTypeIndex.t130 m hm).action.ρ = Type130.ρM := rfl
  have eρ' : (StrothTypeIndex.t131 m hm).action.ρ = Type131.ρM := rfl
  refine ⟨?_, matAct_gen_eq_add_tw _ _ 1 0 0 1 v10 v11 v12,
    matAct_gen_eq_add_tw _ _ 2 0 1 0 v20 v21 v22, ?_,
    matAct_gen_eq_add_tw _ _ 1 0 1 0 w10 w11 w12, matAct_gen_eq_add_tw _ _ 2 0 1 1 w20 w21 w22,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e0 _ _ 0 (by simp [euv, euv', Type130.uvM, Type131.uvM, ofCols_apply])
      (by simp [euv, euv', Type130.uvM, Type131.uvM, ofCols_apply])
      (by simp [euv, euv', Type130.uvM, Type131.uvM, ofCols_apply])
  · exact e0 _ _ 0 (by simp [et, et', Type130.tM, Type131.tM, ofCols_apply])
      (by simp [et, et', Type130.tM, Type131.tM, ofCols_apply])
      (by simp [et, et', Type130.tM, Type131.tM, ofCols_apply])
  all_goals
    first
    | exact e0 _ _ _ (by simp [eu, eu', Type130.uM, Type131.uM])
        (by simp [eu, eu', Type130.uM, Type131.uM]) (by simp [eu, eu', Type130.uM, Type131.uM])
    | exact e0 _ _ _ (by simp [eρ, eρ', Type130.ρM, Type131.ρM])
        (by simp [eρ, eρ', Type130.ρM, Type131.ρM]) (by simp [eρ, eρ', Type130.ρM, Type131.ρM])

theorem hasStrothTypeOver_t130_or_t131_of_data {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t330 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t130 m hm) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t131 m hm) := by
  obtain ⟨cV, cW, cU, cR⟩ := restrict_t330_t130 hm
  rcases hasStrothTypeOver_or_of_index_four_of_data D hBC hC hrel hL hH hcS (t330_k_pos hm)
      (parityTorus_rho_t330 hm) (rho_a_t330 hm) (fix_torus_t330 hm) (fix4_torus_t330 hm)
      (StrothTypeIndex.t130 m hm) rfl rfl rfl (StrothTypeIndex.t131 m hm).action
      (profile4_t130 hm) (twist4_t130 hm) cV cW cU cR with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothTypeOver_of_basisChange D hL (StrothTypeIndex.t131 m hm) E φ h2)

end CFSG.CGT.Stroth77
