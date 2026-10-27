module

public import CFSG.CGT.Stroth77.Extension212Group4
public import CFSG.CGT.Stroth77.Extension212Profile

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem exists_four_nsmul_eq_iff {K : Fin 3 → ℕ} (hk : ∀ i, 2 ≤ K i) (p q r : ℤ) :
    (∃ w : Torus K, 4 • w = p • gen K 0 + q • gen K 1 + r • gen K 2) ↔
      (4 : ℤ) ∣ p ∧ (4 : ℤ) ∣ q ∧ (4 : ℤ) ∣ r := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨a, b, c, rfl⟩ := torus_eq_zsmul_gens K w
    have e : 4 • (a • gen K 0 + b • gen K 1 + c • gen K 2) =
        (4 * a) • gen K 0 + (4 * b) • gen K 1 + (4 * c) • gen K 2 := by
      rw [← natCast_zsmul]
      module
    rw [e] at hw
    obtain ⟨h0, h1, h2⟩ := zsmul_gens_dvd_of_eq hw
    have d4 : ∀ i, (4 : ℤ) ∣ 2 ^ K i := fun i => by
      obtain ⟨t, ht⟩ : ∃ t, K i = t + 2 := ⟨K i - 2, by have := hk i; omega⟩
      rw [ht, pow_add]
      exact ⟨2 ^ t, by ring⟩
    refine ⟨?_, ?_, ?_⟩
    · have := dvd_add ((d4 0).trans h0) (dvd_mul_right (4 : ℤ) a)
      simpa using this
    · have := dvd_add ((d4 1).trans h1) (dvd_mul_right (4 : ℤ) b)
      simpa using this
    · have := dvd_add ((d4 2).trans h2) (dvd_mul_right (4 : ℤ) c)
      simpa using this
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩
    refine ⟨a • gen K 0 + b • gen K 1 + c • gen K 2, ?_⟩
    rw [← natCast_zsmul]
    module

section Base

variable {m : ℕ} (hm : 3 ≤ m)

theorem k_pos_t120 : ∀ i, 1 ≤ (StrothTypeIndex.t120 m hm).k i := by
  intro i; fin_cases i <;> simp [StrothTypeIndex.k, Type120.k] <;> omega

theorem k_two_le_t120 : ∀ i, 2 ≤ (StrothTypeIndex.t120 m hm).k i := by
  intro i; fin_cases i <;> simp [StrothTypeIndex.k, Type120.k] <;> omega

theorem rho_gens_t120 (x y z : ℤ) :
    (StrothTypeIndex.t120 m hm).action.φρ (x • gen _ 0 + y • gen _ 1 + z • gen _ 2) =
      (x - 2 * z) • gen _ 0 + (-z) • gen _ 1 + (y - z) • gen _ 2 := by
  have h0 : (StrothTypeIndex.t120 m hm).action.φρ (gen _ 0) = (1 : ℤ) • gen _ 0 :=
    Type120.rho_c (Type120.data m (by omega))
  have h1 : (StrothTypeIndex.t120 m hm).action.φρ (gen _ 1) = (1 : ℤ) • gen _ 2 :=
    Type120.rho_a (Type120.data m (by omega))
  have h2 : (StrothTypeIndex.t120 m hm).action.φρ (gen _ 2) =
      (-2 : ℤ) • gen _ 0 + (-1 : ℤ) • gen _ 1 + (-1 : ℤ) • gen _ 2 :=
    Type120.rho_b (Type120.data m (by omega))
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, h1, h2]
  module

theorem t_gens_t120 (x y z : ℤ) :
    (StrothTypeIndex.t120 m hm).action.φt (x • gen _ 0 + y • gen _ 1 + z • gen _ 2) =
      (x * (4 - Type120.iV (m + 1)) + y * (4 * Type120.GV (m + 1) * Type120.iV (m + 1)) +
          z * (2 * Type120.FV (m + 1) * Type120.iV (m + 1) - 4 * Type120.iV (m + 1))) • gen _ 0 +
        (x * 2 + y * (-7 * Type120.iV (m + 1)) + z * (-2 * Type120.iV (m + 1))) • gen _ 1 +
        (x * 4 + y * (-8 * Type120.iV (m + 1)) + z * (-7 * Type120.iV (m + 1))) • gen _ 2 := by
  have h0 : (StrothTypeIndex.t120 m hm).action.φt (gen _ 0) =
      (4 - Type120.iV (m + 1)) • gen _ 0 + (2 : ℤ) • gen _ 1 + (4 : ℤ) • gen _ 2 :=
    Type120.t_c (Type120.data m (by omega))
  have h1 : (StrothTypeIndex.t120 m hm).action.φt (gen _ 1) =
      (4 * Type120.GV (m + 1) * Type120.iV (m + 1)) • gen _ 0 +
        (-7 * Type120.iV (m + 1)) • gen _ 1 + (-8 * Type120.iV (m + 1)) • gen _ 2 :=
    Type120.t_a (Type120.data m (by omega))
  have h2 : (StrothTypeIndex.t120 m hm).action.φt (gen _ 2) =
      (2 * Type120.FV (m + 1) * Type120.iV (m + 1) - 4 * Type120.iV (m + 1)) • gen _ 0 +
        (-2 * Type120.iV (m + 1)) • gen _ 1 + (-7 * Type120.iV (m + 1)) • gen _ 2 :=
    Type120.t_b (Type120.data m (by omega))
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, h1, h2]
  module

theorem rhoPar_t120 (v : Torus (StrothTypeIndex.t120 m hm).k) :
    parityTorus _ (k_pos_t120 hm) ((StrothTypeIndex.t120 m hm).action.φρ v) =
      rhoBar300 (parityTorus _ (k_pos_t120 hm) v) := by
  obtain ⟨x, y, z, rfl⟩ := torus_eq_zsmul_gens _ v
  rw [rho_gens_t120, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  funext t
  fin_cases t
  · simp [rhoBar300, h2]
  · simp [rhoBar300, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar300, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem rhoA_t120 :
    (StrothTypeIndex.t120 m hm).action.φρ (gen _ 1) = gen (StrothTypeIndex.t120 m hm).k 2 := by
  have h1 : (StrothTypeIndex.t120 m hm).action.φρ (gen _ 1) = (1 : ℤ) • gen _ 2 :=
    Type120.rho_a (Type120.data m (by omega))
  rw [h1, one_smul]

theorem isCoprime_two_pow_three (e : ℕ) : IsCoprime ((2 : ℤ) ^ e) 3 :=
  (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left

theorem fix_t120 (v : Torus (StrothTypeIndex.t120 m hm).k)
    (hρ : (StrothTypeIndex.t120 m hm).action.φρ v = v)
    (ht : (StrothTypeIndex.t120 m hm).action.φt v = v) : v = 0 := by
  obtain ⟨x, y, z, rfl⟩ := torus_eq_zsmul_gens _ v
  rw [rho_gens_t120] at hρ
  obtain ⟨-, h1, h2⟩ := zsmul_gens_dvd_of_eq hρ
  have hK1 : (StrothTypeIndex.t120 m hm).k 1 = m + 1 := rfl
  have hK2 : (StrothTypeIndex.t120 m hm).k 2 = m + 1 := rfl
  have hK0 : (StrothTypeIndex.t120 m hm).k 0 = m := rfl
  rw [hK1] at h1
  rw [hK2] at h2
  have hz : (2 : ℤ) ^ (m + 1) ∣ z := by
    refine (isCoprime_two_pow_three (m + 1)).dvd_of_dvd_mul_right ?_
    have := dvd_add h1 h2
    convert this using 1
    ring
  have hy : (2 : ℤ) ^ (m + 1) ∣ y := by
    have := dvd_sub h1 hz
    convert this using 1
    ring
  have hv : x • gen (StrothTypeIndex.t120 m hm).k 0 + y • gen _ 1 + z • gen _ 2 =
      x • gen _ 0 + (0 : ℤ) • gen _ 1 + (0 : ℤ) • gen _ 2 :=
    zsmul_gens_eq_of_dvd (by simp) (by rw [hK1]; simpa using hy) (by rw [hK2]; simpa using hz)
  rw [hv] at ht ⊢
  rw [t_gens_t120] at ht
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht
  rw [hK1] at ht1
  have hx : (2 : ℤ) ^ m ∣ x := by
    have h' : (2 : ℤ) ^ m * 2 ∣ 2 * x := by
      rw [← pow_succ]
      have := ht1
      convert (dvd_neg.mpr this) using 1
      ring
    rw [mul_comm (2 : ℤ) x] at h'
    exact (mul_dvd_mul_iff_right two_ne_zero).mp h'
  rw [← zero_zsmul (gen (StrothTypeIndex.t120 m hm).k 0)]
  rw [show (0 : ℤ) • gen (StrothTypeIndex.t120 m hm).k 0 =
      (0 : ℤ) • gen _ 0 + (0 : ℤ) • gen _ 1 + (0 : ℤ) • gen _ 2 by simp]
  exact zsmul_gens_eq_of_dvd (by rw [hK0]; simpa using hx) (by simp) (by simp)

theorem fix4_t120 (v : Torus (StrothTypeIndex.t120 m hm).k)
    (hρ : ∃ z, 4 • z = (StrothTypeIndex.t120 m hm).action.φρ v - v)
    (ht : ∃ z, 4 • z = (StrothTypeIndex.t120 m hm).action.φt v - v) : ∃ z, 2 • z = v := by
  obtain ⟨x, y, z, rfl⟩ := torus_eq_zsmul_gens _ v
  rw [rho_gens_t120] at hρ
  rw [t_gens_t120] at ht
  have eρ : (x - 2 * z) • gen (StrothTypeIndex.t120 m hm).k 0 + (-z) • gen _ 1 +
      (y - z) • gen _ 2 - (x • gen _ 0 + y • gen _ 1 + z • gen _ 2) =
      (-2 * z) • gen _ 0 + (-z - y) • gen _ 1 + (y - 2 * z) • gen _ 2 := by
    module
  rw [eρ, exists_four_nsmul_eq_iff (k_two_le_t120 hm)] at hρ
  obtain ⟨-, h1, h2⟩ := hρ
  have hz : (4 : ℤ) ∣ z := by
    have h3 : (4 : ℤ) ∣ z * 3 := by
      have := dvd_add h1 h2
      have := dvd_neg.mpr this
      convert this using 1
      ring
    exact (show IsCoprime (4 : ℤ) 3 from ⟨1, -1, by norm_num⟩).dvd_of_dvd_mul_right h3
  have hy : (4 : ℤ) ∣ y := by
    have := dvd_add h1 hz
    have := dvd_neg.mpr this
    convert this using 1
    ring
  set i := Type120.iV (m + 1)
  have et : (x * (4 - i) + y * (4 * Type120.GV (m + 1) * i) +
        z * (2 * Type120.FV (m + 1) * i - 4 * i)) • gen (StrothTypeIndex.t120 m hm).k 0 +
      (x * 2 + y * (-7 * i) + z * (-2 * i)) • gen _ 1 +
      (x * 4 + y * (-8 * i) + z * (-7 * i)) • gen _ 2 -
        (x • gen _ 0 + y • gen _ 1 + z • gen _ 2) =
      (x * (4 - i) + y * (4 * Type120.GV (m + 1) * i) +
        z * (2 * Type120.FV (m + 1) * i - 4 * i) - x) • gen _ 0 +
      (x * 2 + y * (-7 * i) + z * (-2 * i) - y) • gen _ 1 +
      (x * 4 + y * (-8 * i) + z * (-7 * i) - z) • gen _ 2 := by
    module
  rw [et, exists_four_nsmul_eq_iff (k_two_le_t120 hm)] at ht
  obtain ⟨-, ht1, -⟩ := ht
  have hx : (2 : ℤ) ∣ x := by
    have h4 : (4 : ℤ) ∣ 2 * x := by
      have := dvd_add (dvd_add (dvd_sub ht1 (hy.mul_left (-7 * i))) (hz.mul_left (2 * i))) hy
      convert this using 1
      ring
    omega
  refine (exists_two_nsmul_eq_iff (k_pos_t120 hm) x y z).2 ⟨even_iff_two_dvd.mpr hx, ?_, ?_⟩
  · exact even_iff_two_dvd.mpr ((show (2 : ℤ) ∣ 4 by norm_num).trans hy)
  · exact even_iff_two_dvd.mpr ((show (2 : ℤ) ∣ 4 by norm_num).trans hz)

end Base

section Target

variable (s : ℕ)

theorem restrict_uv_t120_t220_aux {G P : ℤ} (hP : 3 * G + 7 = 16 * P ^ 2)
    (hPs : (2 : ℤ) ^ s = P) :
    MatEq (Type220.k s)
      (Type220.uvM (8 * (4 * G + 7) + 19) (4 * (4 * G + 7) + 9) (4 * G + 7) * diag4)
      (diag4 * Type120.uvM (8 * G + 19) (4 * G + 9) G) := by
  refine MatEq.of_three_pow_mul_witness 1
    (W := !![
      -96*P, 20480*P^3 - 32*P, -5505024*P^5 - 389120*P^3 - 784*P;
      0, -240*P, -307200*P^3 - 768*P;
      0, 96*P, 30720*P^3 + 192*P]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type220.k, diag4, Matrix.mul_diagonal, Matrix.diagonal_mul, Type220.uvM, Type220.uvA,
      Type220.tM, Type220.ρM, Type220.uM, Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM,
      Type120.uM, uMat, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      pow_add, hPs, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | ring1
    | linear_combination (-1376256*P^4 - 258048*G*P^2 - 48384*G^2 - 699392*P^2 - 244032*G
        - 306180) * hP
    | linear_combination (-24) * hP
    | linear_combination (-240) * hP
    | linear_combination (-307200*P^2 - 57600*G - 135168) * hP
    | linear_combination (30720*P^2 + 5760*G + 13632) * hP
    | linear_combination (5120*P^2 + 960*G + 2232) * hP
    | linear_combination (96) * hP

theorem restrict_t_t120_t220_aux {G P : ℤ} (hP : 3 * G + 7 = 16 * P ^ 2)
    (hPs : (2 : ℤ) ^ s = P) :
    MatEq (Type220.k s)
      (Type220.tM (8 * (4 * G + 7) + 19) (4 * (4 * G + 7) + 9) (4 * G + 7) * diag4)
      (diag4 * Type120.tM (8 * G + 19) (4 * G + 9) G) := by
  refine MatEq.of_three_pow_mul_witness 1
    (W := !![
      -96*P, 10240*P^3 - 880*P, 20480*P^3 - 416*P;
      0, -336*P, -96*P;
      0, -384*P, -336*P]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type220.k, diag4, Matrix.mul_diagonal, Matrix.diagonal_mul, Type220.uvM, Type220.uvA,
      Type220.tM, Type220.ρM, Type220.uM, Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM,
      Type120.uM, uMat, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      pow_add, hPs, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | ring1
    | linear_combination (-24) * hP
    | linear_combination (-336) * hP
    | linear_combination (-384) * hP
    | linear_combination (-96) * hP
    | linear_combination (2560*P^2 + 480*G + 900) * hP
    | linear_combination (5120*P^2 + 960*G + 2136) * hP

theorem restrict_u_t120_t220_aux {G P : ℤ} (hP : 3 * G + 7 = 16 * P ^ 2)
    (hPs : (2 : ℤ) ^ s = P) :
    MatEq (Type220.k s)
      (Type220.uM (8 * (4 * G + 7) + 19) (4 * (4 * G + 7) + 9) (4 * G + 7) * diag4)
      (diag4 * Type120.uM (4 * G + 9)) := by
  refine MatEq.of_three_pow_mul_witness 1
    (W := !![
      0, -192*P, -192*P;
      0, 0, 0;
      0, 0, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type220.k, diag4, Matrix.mul_diagonal, Matrix.diagonal_mul, Type220.uvM, Type220.uvA,
      Type220.tM, Type220.ρM, Type220.uM, Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM,
      Type120.uM, uMat, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      pow_add, hPs, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | ring1
    | linear_combination (-48) * hP

theorem restrict_ρ_t120_t220_aux : MatEq (Type220.k s) (Type220.ρM * diag4)
      (diag4 * Type120.ρM) := by
  refine MatEq.of_eq ?_
  ext r c
  fin_cases r <;> fin_cases c <;> simp [diag4, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Type220.ρM, Type120.ρM, ofCols_apply]

local notation "ι'" => Type120.iV (s + 4)
local notation "φ'" => Type120.FV (s + 4)
local notation "γ'" => Type120.GV (s + 4)

section Matrices

variable (hs : 1 ≤ s)

theorem t220_uv_eq : (StrothTypeIndex.t220 s hs).action.uv = Type220.uvM ι' φ' γ' := rfl
theorem t220_t_eq : (StrothTypeIndex.t220 s hs).action.t = Type220.tM ι' φ' γ' := rfl
theorem t220_u_eq : (StrothTypeIndex.t220 s hs).action.u = Type220.uM ι' φ' γ' := rfl
theorem t220_ρ_eq : (StrothTypeIndex.t220 s hs).action.ρ = Type220.ρM := rfl
theorem t221_uv_eq : (StrothTypeIndex.t221 s hs).action.uv = Type221.uvM s ι' φ' γ' := rfl
theorem t221_t_eq : (StrothTypeIndex.t221 s hs).action.t = Type221.tM s ι' φ' γ' := rfl
theorem t221_u_eq : (StrothTypeIndex.t221 s hs).action.u = Type221.uM s ι' φ' γ' := rfl
theorem t221_ρ_eq : (StrothTypeIndex.t221 s hs).action.ρ = Type221.ρM := rfl

end Matrices

theorem profile4_t220 (hs : 1 ≤ s) :
    Profile4 (StrothTypeIndex.t220 s hs).k (StrothTypeIndex.t220 s hs).action.φuv
      (StrothTypeIndex.t220 s hs).action.φt (StrothTypeIndex.t220 s hs).action.φu
      (StrothTypeIndex.t220 s hs).action.φρ := by
  have hi := iV_cast_two (s + 4)
  have hF := FV_cast_two_succ (s + 3)
  have hG := GV_cast_two_add_two (s + 2)
  refine profile4_of_par (k := s + 2) (n := s + 4) rfl (by omega) (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  all_goals simp only [t220_uv_eq, t220_t_eq, t220_u_eq, t220_ρ_eq]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (apply odd_of_cast_two; simp [Type220.uvM, Type220.uvA, Type220.tM, Type220.ρM,
        ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide)
    | (apply even_of_cast_two; simp [Type220.uvM, Type220.uvA, Type220.tM, Type220.ρM,
        ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (apply odd_of_cast_two; simp [Type220.tM, Type220.uvA, Type220.ρM, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide)
    | (apply even_of_cast_two; simp [Type220.tM, Type220.uvA, Type220.ρM, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three, hi, hF, hG] <;> decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (apply odd_of_cast_two; simp [Type220.uM, uMat, ofCols_apply, hF] <;> decide)
    | (apply even_of_cast_two; simp [Type220.uM, uMat, ofCols_apply, hF] <;> decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (apply odd_of_cast_two; simp [Type220.ρM, ofCols_apply] <;> decide)
    | (apply even_of_cast_two; simp [Type220.ρM, ofCols_apply] <;> decide)
  · exact ⟨1, -1, by simp [Type220.uvM, ofCols_apply], by simp [Type220.uvM, ofCols_apply],
      by decide, by decide⟩
  · exact ⟨1, 2, by simp [Type220.tM, ofCols_apply], by simp [Type220.tM, ofCols_apply],
      by decide, by decide⟩
  · exact ⟨0, 0, by simp [Type220.uM, uMat, ofCols_apply], by simp [Type220.uM, uMat,
      ofCols_apply], by decide, by decide⟩
  · exact ⟨0, 0, by simp [Type220.ρM, ofCols_apply], by simp [Type220.ρM, ofCols_apply],
      by decide, by decide⟩

theorem twist4_t220 (hs : 1 ≤ s) :
    Twist4 (StrothTypeIndex.t220 s hs).k (StrothTypeIndex.t220 s hs).action.φuv
      (StrothTypeIndex.t220 s hs).action.φt (StrothTypeIndex.t220 s hs).action.φu
      (StrothTypeIndex.t220 s hs).action.φρ (StrothTypeIndex.t221 s hs).action.φuv
      (StrothTypeIndex.t221 s hs).action.φt (StrothTypeIndex.t221 s hs).action.φu
      (StrothTypeIndex.t221 s hs).action.φρ := by
  have hK0 : (StrothTypeIndex.t220 s hs).k 0 = s + 2 := rfl
  have hK1 : (StrothTypeIndex.t220 s hs).k 1 = s + 4 := rfl
  have hK2 : (StrothTypeIndex.t220 s hs).k 2 = s + 4 := rfl
  have hK0' : (StrothTypeIndex.t221 s hs).k 0 = s + 2 := rfl
  have hK1' : (StrothTypeIndex.t221 s hs).k 1 = s + 4 := rfl
  have hK2' : (StrothTypeIndex.t221 s hs).k 2 = s + 4 := rfl
  have hi : ι' = 8 * γ' + 19 := (Type220.data s).hi
  have e0 {M M' : IntMat} (hM : Compat (StrothTypeIndex.t220 s hs).k M)
      (hM' : Compat (StrothTypeIndex.t220 s hs).k M') (j : Fin 3)
      (h0 : M 0 j = M' 0 j) (h1 : M 1 j = M' 1 j) (h2 : M 2 j = M' 2 j) :
      matAct _ M' hM' (gen _ j) = matAct _ M hM (gen _ j) := by
    rw [matAct_gen_eq, matAct_gen_eq, h0, h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e0 _ _ 0 (by simp [t220_uv_eq, t221_uv_eq, Type220.uvM, Type221.uvM, ofCols_apply])
      (by simp [t220_uv_eq, t221_uv_eq, Type220.uvM, Type221.uvM, ofCols_apply])
      (by simp [t220_uv_eq, t221_uv_eq, Type220.uvM, Type221.uvM, ofCols_apply])
  · refine matAct_gen_eq_add_tw _ _ 1 0 0 1 ?_ ?_ ?_ <;>
      simp [hK0, hK1, hK2, hK0', hK1', hK2', t220_uv_eq, t221_uv_eq, Type220.uvM, Type221.uvM,
        Type220.uvA, Type221.uvA, ofCols_apply] <;>
      ring_nf <;> simp
  · refine matAct_gen_eq_add_tw _ _ 2 0 1 0 ?_ ?_ ?_ <;>
      simp only [hK0, hK1, hK2, hK0', hK1', hK2', t220_uv_eq, t221_uv_eq]
    · exact ⟨-2 * ι' * φ' - 10 * ι', by
        simp [Type220.uvM, Type221.uvM, Type220.uvA, Type221.uvA, Type220.tM, Type221.tM,
          Type220.ρM, Type221.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨-36 * γ' - 85 - 4 * 2 ^ s, by
        simp [Type220.uvM, Type221.uvM, Type220.uvA, Type221.uvA, Type220.tM, Type221.tM,
          Type220.ρM, Type221.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        rw [hi]
        ring⟩
    · exact ⟨0, by
        simp [Type220.uvM, Type221.uvM, Type220.uvA, Type221.uvA, Type220.tM, Type221.tM,
          Type220.ρM, Type221.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
  · exact e0 _ _ 0 (by simp [t220_t_eq, t221_t_eq, Type220.tM, Type221.tM, ofCols_apply])
      (by simp [t220_t_eq, t221_t_eq, Type220.tM, Type221.tM, ofCols_apply])
      (by simp [t220_t_eq, t221_t_eq, Type220.tM, Type221.tM, ofCols_apply])
  · refine matAct_gen_eq_add_tw _ _ 1 0 1 0 ?_ ?_ ?_ <;>
      simp [hK0, hK1, hK2, hK0', hK1', hK2', t220_t_eq, t221_t_eq, Type220.tM, Type221.tM,
        ofCols_apply] <;>
      ring_nf <;> simp
  · refine matAct_gen_eq_add_tw _ _ 2 0 1 1 ?_ ?_ ?_ <;>
      simp only [hK0, hK1, hK2, hK0', hK1', hK2', t220_t_eq, t221_t_eq]
    · exact ⟨2, by
        simp [Type220.tM, Type221.tM, Type220.uvA, Type221.uvA, Type220.ρM, Type221.ρM,
          ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨1, by
        simp [Type220.tM, Type221.tM, Type220.uvA, Type221.uvA, Type220.ρM, Type221.ρM,
          ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
    · exact ⟨1, by
        simp [Type220.tM, Type221.tM, Type220.uvA, Type221.uvA, Type220.ρM, Type221.ρM,
          ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring⟩
  · exact e0 _ _ 0 (by simp [t220_u_eq, t221_u_eq, Type220.uM, Type221.uM, uMat, ofCols_apply])
      (by simp [t220_u_eq, t221_u_eq, Type220.uM, Type221.uM, uMat, ofCols_apply])
      (by simp [t220_u_eq, t221_u_eq, Type220.uM, Type221.uM, uMat, ofCols_apply])
  · exact e0 _ _ 1 (by simp [t220_u_eq, t221_u_eq, Type220.uM, Type221.uM, uMat, ofCols_apply])
      (by simp [t220_u_eq, t221_u_eq, Type220.uM, Type221.uM, uMat, ofCols_apply])
      (by simp [t220_u_eq, t221_u_eq, Type220.uM, Type221.uM, uMat, ofCols_apply])
  · exact e0 _ _ 2 (by simp [t220_u_eq, t221_u_eq, Type220.uM, Type221.uM, uMat, ofCols_apply])
      (by simp [t220_u_eq, t221_u_eq, Type220.uM, Type221.uM, uMat, ofCols_apply])
      (by simp [t220_u_eq, t221_u_eq, Type220.uM, Type221.uM, uMat, ofCols_apply])
  · exact e0 _ _ 0 (by simp [t220_ρ_eq, t221_ρ_eq, Type220.ρM, Type221.ρM, ofCols_apply])
      (by simp [t220_ρ_eq, t221_ρ_eq, Type220.ρM, Type221.ρM, ofCols_apply])
      (by simp [t220_ρ_eq, t221_ρ_eq, Type220.ρM, Type221.ρM, ofCols_apply])
  · exact e0 _ _ 1 (by simp [t220_ρ_eq, t221_ρ_eq, Type220.ρM, Type221.ρM, ofCols_apply])
      (by simp [t220_ρ_eq, t221_ρ_eq, Type220.ρM, Type221.ρM, ofCols_apply])
      (by simp [t220_ρ_eq, t221_ρ_eq, Type220.ρM, Type221.ρM, ofCols_apply])
  · exact e0 _ _ 2 (by simp [t220_ρ_eq, t221_ρ_eq, Type220.ρM, Type221.ρM, ofCols_apply])
      (by simp [t220_ρ_eq, t221_ρ_eq, Type220.ρM, Type221.ρM, ofCols_apply])
      (by simp [t220_ρ_eq, t221_ρ_eq, Type220.ρM, Type221.ρM, ofCols_apply])

theorem restrict_t120_t220 (hs : 1 ≤ s) (hm : 3 ≤ s + 2) :
    MatEq (StrothTypeIndex.t220 s hs).k ((StrothTypeIndex.t220 s hs).action.uv * diag4)
        (diag4 * (StrothTypeIndex.t120 (s + 2) hm).action.uv) ∧
      MatEq (StrothTypeIndex.t220 s hs).k ((StrothTypeIndex.t220 s hs).action.t * diag4)
        (diag4 * (StrothTypeIndex.t120 (s + 2) hm).action.t) ∧
      MatEq (StrothTypeIndex.t220 s hs).k ((StrothTypeIndex.t220 s hs).action.u * diag4)
        (diag4 * (StrothTypeIndex.t120 (s + 2) hm).action.u) ∧
      MatEq (StrothTypeIndex.t220 s hs).k ((StrothTypeIndex.t220 s hs).action.ρ * diag4)
        (diag4 * (StrothTypeIndex.t120 (s + 2) hm).action.ρ) := by
  set G := Type120.GV (s + 2 + 1) with hGdef
  have e120uv : (StrothTypeIndex.t120 (s + 2) hm).action.uv =
      Type120.uvM (Type120.iV (s + 2 + 1)) (Type120.FV (s + 2 + 1)) G := rfl
  have e120t : (StrothTypeIndex.t120 (s + 2) hm).action.t =
      Type120.tM (Type120.iV (s + 2 + 1)) (Type120.FV (s + 2 + 1)) G := rfl
  have e120u : (StrothTypeIndex.t120 (s + 2) hm).action.u = Type120.uM (Type120.FV (s + 2 + 1)) :=
    rfl
  have e120ρ : (StrothTypeIndex.t120 (s + 2) hm).action.ρ = Type120.ρM := rfl
  obtain ⟨hi, hF, -⟩ := Type120.data (s + 2) (by omega)
  obtain ⟨hi', hF', hG', -⟩ := Type220.data s
  have hP : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2 := by
    have h := Type120.three_mul_GV (s + 2 + 1)
    rw [show s + 2 + 1 - 1 = s + 2 by omega, pow_add, four_pow_eq_two_pow_sq] at h
    rw [hGdef]
    linarith
  have hGG : Type120.GV (s + 4) = 4 * G + 7 := by
    generalize ((2 : ℤ) ^ s) ^ 2 = X at hP hG'
    omega
  have hi'' : Type120.iV (s + 4) = 8 * (4 * G + 7) + 19 := by rw [hi', hGG]
  have hF'' : Type120.FV (s + 4) = 4 * (4 * G + 7) + 9 := by rw [hF', hGG]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [t220_uv_eq, e120uv, hi'', hF'', hGG, hi, hF]
    exact restrict_uv_t120_t220_aux s hP rfl
  · rw [t220_t_eq, e120t, hi'', hF'', hGG, hi, hF]
    exact restrict_t_t120_t220_aux s hP rfl
  · rw [t220_u_eq, e120u, hi'', hF'', hGG, hF]
    exact restrict_u_t120_t220_aux s hP rfl
  · rw [t220_ρ_eq, e120ρ]
    exact restrict_ρ_t120_t220_aux s

end Target

theorem hasStrothType_t220_or_t221_of_data_aux {s : ℕ} {hm : 3 ≤ s + 2}
    (D : StrothTypeData B (StrothTypeIndex.t120 (s + 2) hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothType C (StrothTypeIndex.t220 s (by omega)) ∨
      HasStrothType C (StrothTypeIndex.t221 s (by omega)) := by
  have hs : 1 ≤ s := by omega
  obtain ⟨cV, cW, cU, cR⟩ := restrict_t120_t220 s hs hm
  rcases hasStrothType_or_of_index_four_of_data D hBC hC hrel hL hH hcS (k_pos_t120 hm)
      (rhoPar_t120 hm) (rhoA_t120 hm) (fix_t120 hm) (fix4_t120 hm) (StrothTypeIndex.t220 s hs)
      rfl rfl rfl (StrothTypeIndex.t221 s hs).action (profile4_t220 s hs) (twist4_t220 s hs)
      cV cW cU cR with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothType_of_basisChange D hL (StrothTypeIndex.t221 s hs) E φ h2)

theorem hasStrothType_t220_or_t221_of_data {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t120 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothType C (StrothTypeIndex.t220 (m - 2) (by omega)) ∨
      HasStrothType C (StrothTypeIndex.t221 (m - 2) (by omega)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  exact hasStrothType_t220_or_t221_of_data_aux D hBC hC hrel hL hH hcS

theorem hasStrothTypeOver_t220_or_t221_of_data_aux {s : ℕ} {hm : 3 ≤ s + 2}
    (D : StrothTypeData B (StrothTypeIndex.t120 (s + 2) hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t220 s (by omega)) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t221 s (by omega)) := by
  have hs : 1 ≤ s := by omega
  obtain ⟨cV, cW, cU, cR⟩ := restrict_t120_t220 s hs hm
  rcases hasStrothTypeOver_or_of_index_four_of_data D hBC hC hrel hL hH hcS (k_pos_t120 hm)
      (rhoPar_t120 hm) (rhoA_t120 hm) (fix_t120 hm) (fix4_t120 hm) (StrothTypeIndex.t220 s hs)
      rfl rfl rfl (StrothTypeIndex.t221 s hs).action (profile4_t220 s hs) (twist4_t220 s hs)
      cV cW cU cR with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothTypeOver_of_basisChange D hL (StrothTypeIndex.t221 s hs) E φ h2)

theorem hasStrothTypeOver_t220_or_t221_of_data {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t120 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t220 (m - 2) (by omega)) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t221 (m - 2) (by omega)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  exact hasStrothTypeOver_t220_or_t221_of_data_aux D hBC hC hrel hL hH hcS

end CFSG.CGT.Stroth77
