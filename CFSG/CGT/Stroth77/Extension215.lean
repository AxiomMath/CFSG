module

public import CFSG.CGT.Stroth77.Extension25Common
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Stroth77.Extension22FourC4
public import CFSG.CGT.Stroth77.TorusCard
public import CFSG.Foundations

local notation "𝔤" m:max j:max => CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type130.k m) j

local notation "𝔥" m:max hm:max j:max =>
  CFSG.CGT.Stroth77.gen
    (CFSG.CGT.Stroth77.StrothTypeIndex.k (CFSG.CGT.Stroth77.StrothTypeIndex.t130 m hm)) j

public section

namespace CFSG.CGT.Stroth77

section Torus

variable {m : ℕ} {i F G N K J : ℤ} (h : Type130.Data m i F G N K J)

theorem u_apply_gens_t130 (x y w : ℤ) :
    (Type130.action h).φu (x • 𝔤 m 0 + y • 𝔤 m 1 + w • 𝔤 m 2) =
      ((-1 + K) * x + (-4 * F) * y + 4 * F * (-1 + K) * w) • 𝔤 m 0 + w • 𝔤 m 1 +
        y • 𝔤 m 2 := by
  rw [matAct_zsmul_gens]
  simp [Type130.action, SigmaFourAction.ofMatEq, Type130.uM, uMat, ofCols_apply]

theorem no_cocycle_u_t130 (hm : 3 ≤ m) (z : Torus (Type130.k m))
    (h1 : 2 • z = (Type130.action h).φu (𝔤 m 0) - 𝔤 m 0)
    (h2 : z + (Type130.action h).φu z = 0) : False := by
  obtain ⟨z0, z1, z2, rfl⟩ := torus_eq_zsmul_gens _ z
  have hc := u_apply_gens_t130 h 1 0 0
  simp only [one_smul, zero_smul, add_zero, mul_one, mul_zero] at hc
  rw [hc] at h1
  rw [u_apply_gens_t130] at h2
  have e1 : (2 * z0) • 𝔤 m 0 + (2 * z1) • 𝔤 m 1 + (2 * z2) • 𝔤 m 2 =
      (-1 + K - 1) • 𝔤 m 0 + (0 : ℤ) • 𝔤 m 1 + (0 : ℤ) • 𝔤 m 2 := by
    linear_combination (norm := module) h1
  have e2 : (z0 + ((-1 + K) * z0 + (-4 * F) * z1 + 4 * F * (-1 + K) * z2)) • 𝔤 m 0 +
      (z1 + z2) • 𝔤 m 1 + (z2 + z1) • 𝔤 m 2 =
      (0 : ℤ) • 𝔤 m 0 + (0 : ℤ) • 𝔤 m 1 + (0 : ℤ) • 𝔤 m 2 := by
    linear_combination (norm := module) h2
  obtain ⟨d0, d1, d2⟩ := zsmul_gens_dvd_of_eq e1
  obtain ⟨f0, -, -⟩ := zsmul_gens_dvd_of_eq e2
  change (2 : ℤ) ^ m ∣ _ at d0 f0
  change (2 : ℤ) ^ (m + 1) ∣ _ at d1 d2
  obtain ⟨-, -, hN, hK, hJ, -⟩ := h
  have hN' : (2 : ℤ) ^ m = 4 * J := by rw [← hN, hK, hJ]; ring
  have h2N : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, hN']; ring
  rw [hN'] at d0 f0
  rw [h2N] at d1 d2
  obtain ⟨P, hP⟩ : ∃ P : ℤ, J = 2 * P := by
    refine ⟨2 ^ (m - 3), ?_⟩
    have : (2 : ℤ) ^ m = 8 * 2 ^ (m - 3) := by
      rw [show m = (m - 3) + 3 by omega, pow_add]
      norm_num [mul_comm]
    linarith
  subst hP
  subst hJ
  obtain ⟨a0, ha0⟩ := d0
  obtain ⟨a1, ha1⟩ := d1
  obtain ⟨a2, ha2⟩ := d2
  obtain ⟨q, hq⟩ := f0
  have hz1 : z1 = -(4 * (2 * P) * a1) := by linarith
  have hz2 : z2 = -(4 * (2 * P) * a2) := by linarith
  subst hz1 hz2
  have hP0 : (2 * (2 * P)) ≠ 0 := by
    intro h0
    have : (0 : ℤ) < 2 ^ m := by positivity
    linarith
  have hz0 : (2 * (2 * P)) * z0 = (2 * (2 * P)) *
      (2 * (-q - 4 * F * a1 + 4 * F * (-1 + 2 * (2 * P)) * a2)) := by
    linear_combination -hq
  have hz0' := mul_left_cancel₀ hP0 hz0
  obtain ⟨w, hw⟩ : ∃ w, z0 = 2 * w := ⟨_, hz0'⟩
  have ha0' : -2 + 4 * P - 2 * z0 = 8 * (P * a0) := by linear_combination ha0
  omega

theorem uvM_apply_t130 (i F G N : ℤ) :
    Type130.uvM i F G N 0 1 = 2 * i * F ∧ Type130.uvM i F G N 1 1 = -5 * i ∧
      Type130.uvM i F G N 2 1 = 2 * i ∧ Type130.uvM i F G N 1 0 = N + 2 ∧
      Type130.uvM i F G N 2 0 = -2 ∧
      Type130.uvM i F G N 1 2 = -2 * i * F * N - 26 * i ^ 2 - 8 * i * F ∧
      Type130.uvM i F G N 2 2 = -2 * i * F * N + 5 * i ^ 2 - 4 * i * F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Type130.uvM, Type130.tM, Type130.uvA, Type130.ρM, ofCols_apply, Matrix.mulVec,
      Matrix.mul_apply, dotProduct, Fin.sum_univ_three] <;> ring

theorem no_cocycle_index_four_t130 (z : Torus (Type130.k m))
    (h1 : 2 • z = (Type130.action h).φuv (𝔤 m 1) - 𝔤 m 1)
    (h2 : z + (Type130.action h).φuv z = 0) : False := by
  obtain ⟨z0, z1, z2, rfl⟩ := torus_eq_zsmul_gens _ z
  have ha := matAct_zsmul_gens (k := Type130.k m) (Type130.action h).uv
    (Type130.action h).compat_uv 0 1 0
  simp only [zero_smul, one_smul, zero_add, add_zero, mul_zero, mul_one] at ha
  have h1' : 2 • (z0 • 𝔤 m 0 + z1 • 𝔤 m 1 + z2 • 𝔤 m 2) =
      (Type130.action h).uv 0 1 • 𝔤 m 0 + (Type130.action h).uv 1 1 • 𝔤 m 1 +
        (Type130.action h).uv 2 1 • 𝔤 m 2 - 𝔤 m 1 := by
    rw [h1]
    exact congrArg (· - 𝔤 m 1) ha
  have h2' := h2
  change _ + matAct _ (Type130.action h).uv (Type130.action h).compat_uv _ = 0 at h2'
  rw [matAct_zsmul_gens] at h2'
  have e1 : (2 * z0) • 𝔤 m 0 + (2 * z1) • 𝔤 m 1 + (2 * z2) • 𝔤 m 2 =
      (Type130.action h).uv 0 1 • 𝔤 m 0 + ((Type130.action h).uv 1 1 - 1) • 𝔤 m 1 +
        (Type130.action h).uv 2 1 • 𝔤 m 2 := by
    linear_combination (norm := module) h1'
  set M := (Type130.action h).uv with hM
  have e2 : (z0 + (M 0 0 * z0 + M 0 1 * z1 + M 0 2 * z2)) • 𝔤 m 0 +
      (z1 + (M 1 0 * z0 + M 1 1 * z1 + M 1 2 * z2)) • 𝔤 m 1 +
      (z2 + (M 2 0 * z0 + M 2 1 * z1 + M 2 2 * z2)) • 𝔤 m 2 =
      (0 : ℤ) • 𝔤 m 0 + (0 : ℤ) • 𝔤 m 1 + (0 : ℤ) • 𝔤 m 2 := by
    linear_combination (norm := module) h2'
  obtain ⟨d0, d1, d2⟩ := zsmul_gens_dvd_of_eq e1
  obtain ⟨-, f1, f2⟩ := zsmul_gens_dvd_of_eq e2
  have hsum := dvd_add f1 f2
  change (2 : ℤ) ^ m ∣ _ at d0
  change (2 : ℤ) ^ (m + 1) ∣ _ at d1 d2 hsum
  have hMe : M = Type130.uvM i F G N := rfl
  rw [hMe] at d0 d1 d2 hsum
  obtain ⟨e01, e11, e21, e10, e20, e12, e22⟩ := uvM_apply_t130 i F G N
  rw [e01] at d0
  rw [e11] at d1
  rw [e21] at d2
  rw [e10, e11, e12, e20, e21, e22] at hsum
  clear e1 e2 f1 f2 h1 h1' h2 h2' ha hM
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi hF hK hJ
  have hN' : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h2N : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, hN']; ring
  rw [hN'] at d0
  rw [h2N] at d1 d2 hsum
  obtain ⟨w0, hw0⟩ := d0
  obtain ⟨w1, hw1⟩ := d1
  obtain ⟨w2, hw2⟩ := d2
  obtain ⟨q, hq⟩ := hsum
  have hz0 : z0 = (4 * G + 9) * (8 * G + 19) - 2 * J * w0 := by linarith
  have hz1 : z1 = -20 * G - 48 - 4 * J * w1 := by linarith
  have hz2 : z2 = (8 * G + 19) - 4 * J * w2 := by linarith
  subst hz0 hz1 hz2
  have hJ0 : (4 * J) ≠ 0 := by
    intro h0
    have : (0 : ℤ) < 2 ^ m := by positivity
    linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = -256 * G ^ 2 * J * w2 + 512 * G ^ 3 + 9216 * G ^ 2 * J -
      864 * G ^ 2 * w2 - 1184 * G * J * w2 + 3568 * G ^ 2 + 43584 * G * J + J * w0 -
      12 * G * w1 - 4080 * G * w2 - 1368 * J * w2 + 8286 * G + 51520 * J - 28 * w1 -
      4816 * w2 + 6412 := ⟨_, rfl⟩
  have key : 4 * J * (2 * Y + 1) = 4 * J * (2 * q) := by
    linear_combination 8 * J * hY + hq + (-4608 * G ^ 2 - 21792 * G - 25760) * hG
  have := mul_left_cancel₀ hJ0 key
  omega

end Torus

theorem t130_k_pos {m : ℕ} (hm : 3 ≤ m) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t130 m hm).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type130.k] <;> omega

theorem rho_apply_gens_t130 {m : ℕ} (hm : 3 ≤ m) (x y w : ℤ) :
    (StrothTypeIndex.t130 m hm).action.φρ (x • 𝔥 m hm 0 + y • 𝔥 m hm 1 + w • 𝔥 m hm 2) =
      (x - 2 * w) • 𝔥 m hm 0 + (-w) • 𝔥 m hm 1 + (y - w) • 𝔥 m hm 2 := by
  rw [matAct_zsmul_gens]
  simp [StrothTypeIndex.action, Type130.actionPaper, Type130.action, SigmaFourAction.ofMatEq,
    Type130.ρM, ofCols_apply]
  ring_nf

theorem parityTorus_rho_t130 {m : ℕ} (hm : 3 ≤ m) (y : Torus (StrothTypeIndex.t130 m hm).k) :
    parityTorus _ (t130_k_pos hm) ((StrothTypeIndex.t130 m hm).action.φρ y) =
      rhoBar300 (parityTorus _ (t130_k_pos hm) y) := by
  obtain ⟨x, y', w, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t130, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r
  · simp [rhoBar300, h2]
  · simp [rhoBar300, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar300, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem odd_iV_t130 (m : ℕ) (hm : 2 ≤ m) : Odd (Type120.iV (m + 1)) := by
  obtain ⟨hi, -⟩ := Type130.data m hm
  exact ⟨4 * Type120.GV (m + 1) + 9, by rw [hi]; ring⟩

theorem parityTorus_uv_a_t130 {m : ℕ} (hm : 3 ≤ m) :
    parityTorus _ (t130_k_pos hm) ((StrothTypeIndex.t130 m hm).action.φuv Torus.a) =
      Pi.single 1 1 := by
  have hI : ((Type120.iV (m + 1) : ℤ) : ZMod 2) = 1 :=
    ZMod.intCast_eq_one_iff_odd.mpr (odd_iV_t130 m (by omega))
  have h := matAct_zsmul_gens (k := (StrothTypeIndex.t130 m hm).k)
    (StrothTypeIndex.t130 m hm).action.uv (StrothTypeIndex.t130 m hm).action.compat_uv 0 1 0
  simp only [zero_smul, one_smul, zero_add, add_zero, mul_zero, mul_one] at h
  rw [Torus.a, h, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h5 : (5 : ZMod 2) = 1 := by decide
  funext r
  fin_cases r <;>
    simp [StrothTypeIndex.action, Type130.actionPaper, Type130.action, SigmaFourAction.ofMatEq,
      Type130.uvM, Type130.uvA, ofCols_apply, hI, h2, h5]

theorem t_c_t130 {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t130 m hm).action.φt (𝔥 m hm 0) =
      (4 - Type120.iV (m + 1)) • 𝔥 m hm 0 + (2 : ℤ) • 𝔥 m hm 1 + (4 + 2 ^ m : ℤ) • 𝔥 m hm 2 := by
  have h := matAct_zsmul_gens (k := (StrothTypeIndex.t130 m hm).k)
    (StrothTypeIndex.t130 m hm).action.t (StrothTypeIndex.t130 m hm).action.compat_t 1 0 0
  simp only [zero_smul, one_smul, add_zero, mul_zero, mul_one] at h
  rw [h]
  simp [StrothTypeIndex.action, Type130.actionPaper, Type130.action, SigmaFourAction.ofMatEq,
    Type130.tM, ofCols_apply]

theorem fixed_rho_t_t130 {S : Type*} [Group S] [Finite S] {B : Subgroup S} {m : ℕ}
    {hm : 3 ≤ m} (D : StrothTypeData B (StrothTypeIndex.t130 m hm)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t130 m hm).action.φρ (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t130 m hm).action.φρ (D.ec y) from
      D.ρ_conj y, hρ]
  have ht' : (StrothTypeIndex.t130 m hm).action.φt (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t130 m hm).action.φt (D.ec y) from
      D.t_conj y, ht]
  apply D.ec_eq_zero_iff.mp
  obtain ⟨x, j, l, hy⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t130 m hm).k (D.ec y)
  rw [hy] at hρ' ht' ⊢
  rw [rho_apply_gens_t130] at hρ'
  obtain ⟨h0, h1, h2⟩ := zsmul_gens_dvd_of_eq hρ'
  change (2 : ℤ) ^ m ∣ _ at h0
  change (2 : ℤ) ^ (m + 1) ∣ _ at h1
  change (2 : ℤ) ^ (m + 1) ∣ _ at h2
  have hl : (2 : ℤ) ^ (m + 1) ∣ l := by
    have h4 : (2 : ℤ) ^ (m + 1) ∣ 4 * l := by
      obtain ⟨w, hw⟩ := h0
      refine ⟨w, ?_⟩
      rw [show (4 : ℤ) * l = 2 * (x - (x - 2 * l)) by ring, hw]
      ring
    have h3 : (2 : ℤ) ^ (m + 1) ∣ 3 * l := by
      rw [show (3 : ℤ) * l = (j - -l) + (l - (j - l)) by ring]
      exact dvd_add h1 h2
    rw [show l = 4 * l - 3 * l by ring]
    exact dvd_sub h4 h3
  have hj : (2 : ℤ) ^ (m + 1) ∣ j := by
    rw [show j = (j - -l) - l by ring]
    exact dvd_sub h1 hl
  have hjl : j • 𝔥 m hm 1 + l • 𝔥 m hm 2 = 0 := by
    rw [(zsmul_gen_eq_zero 1 j).mpr, (zsmul_gen_eq_zero 2 l).mpr, add_zero]
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd l _).mpr (by exact_mod_cast hl)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd j _).mpr (by exact_mod_cast hj)
  rw [add_assoc, hjl, add_zero] at ht' ⊢
  rw [map_zsmul, t_c_t130] at ht'
  have h' : ((4 - Type120.iV (m + 1)) * x) • 𝔥 m hm 0 + (2 * x) • 𝔥 m hm 1 +
      ((4 + 2 ^ m) * x) • 𝔥 m hm 2 = x • 𝔥 m hm 0 + (0 : ℤ) • 𝔥 m hm 1 + (0 : ℤ) • 𝔥 m hm 2 := by
    linear_combination (norm := module) ht'
  obtain ⟨-, hx1, -⟩ := zsmul_gens_dvd_of_eq h'
  change (2 : ℤ) ^ (m + 1) ∣ _ at hx1
  have hx : (2 : ℤ) ^ m ∣ x := by
    rw [show (0 : ℤ) - 2 * x = 2 * (-x) by ring, pow_succ, mul_comm _ (2 : ℤ)] at hx1
    exact dvd_neg.mp ((mul_dvd_mul_iff_left two_ne_zero).mp hx1)
  exact (zsmul_gen_eq_zero 0 x).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd x _).mpr
    (by exact_mod_cast hx))

section Lemma

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ} {hm : 3 ≤ m}

theorem false_of_index_two_of_data_t130 (D : StrothTypeData B (StrothTypeIndex.t130 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have huc : ∀ x : B, D.ec (conjBy D.u_mem x) =
      (StrothTypeIndex.t130 m hm).action.φu (D.ec x) := D.u_conj
  obtain ⟨z, h1, h2⟩ := exists_cocycle_involution_index_two_of_data_Idx4 D (t130_k_pos hm)
    (parityTorus_rho_t130 hm) (fun v h1 h2 => rhoBar300_fixed_check v ⟨h1, h2⟩) hBC hC hrel hL
    hH hcS (hL D.u_mem_L) D.u_mem D.u_sq huc
  exact no_cocycle_u_t130 (Type130.data m (by omega)) hm z h1 h2

theorem false_of_index_two_t130 (hB : HasStrothType B (StrothTypeIndex.t130 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_two_of_data_t130 hB.data hBC hC hrel hL hH hcS

theorem false_of_index_four_of_data_t130 (D : StrothTypeData B (StrothTypeIndex.t130 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  haveI hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  by_cases hcyc : IsCyclic (C ⧸ B.subgroupOf C)
  · obtain ⟨C₂, hBC₂, hC₂C, hrel₂, hL₂⟩ :=
      exists_index_two_of_isCyclic_Idx4 D hBC hC hrel hL hcyc
    exact false_of_index_two_of_data_t130 D hBC₂ (hC₂C.trans hC) hrel₂ hL₂ hH (hC₂C.trans hcS)
  · obtain ⟨z, h1, h2⟩ := exists_cocycle_index_four_of_data_Idx4 D (t130_k_pos hm)
      (parityTorus_rho_t130 hm) (fun _ hρ ht => fixed_rho_t_t130 D hρ ht)
      (parityTorus_uv_a_t130 hm) hBC hC hrel hL hH hcS hcyc
    exact no_cocycle_index_four_t130 (Type130.data m (by omega)) z h1 h2

theorem false_of_index_four_t130 (hB : HasStrothType B (StrothTypeIndex.t130 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_four_of_data_t130 hB.data hBC hC hrel hL hH hcS

end Lemma

end CFSG.CGT.Stroth77
