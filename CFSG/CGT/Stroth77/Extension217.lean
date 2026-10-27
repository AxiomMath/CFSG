module

public import CFSG.CGT.Stroth77.Extension25Common
public import CFSG.CGT.Stroth77.TorusNormalForm

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem t121_k_pos {m : ℕ} (hm : 3 ≤ m) (i : Fin 3) : 1 ≤ Type121.k m i := by
  fin_cases i <;> simp [Type121.k] <;> omega

theorem torus_c_eq_ofInt_t121 (k : Fin 3 → ℕ) :
    (Torus.c : Torus k) = Torus.ofInt k ![1, 0, 0] := by
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem torus_a_eq_ofInt_t121 (k : Fin 3 → ℕ) :
    (Torus.a : Torus k) = Torus.ofInt k ![0, 1, 0] := by
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem parityTorus_ofInt_t121 {k : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) (v : Fin 3 → ℤ) :
    parityTorus k hk (Torus.ofInt k v) = ![(v 0 : ZMod 2), (v 1 : ZMod 2), (v 2 : ZMod 2)] := by
  rw [Torus.ofInt_eq_zsmul_gens, parityTorus_zsmul_gens]

theorem parityTorus_rho_t121 {m : ℕ} (hm : 3 ≤ m) (y : Torus (StrothTypeIndex.t121 m hm).k) :
    parityTorus _ (t121_k_pos hm) ((StrothTypeIndex.t121 m hm).action.φρ y) =
      rhoBar300 (parityTorus _ (t121_k_pos hm) y) := by
  change parityTorus (Type121.k m) (t121_k_pos hm) (matAct (Type121.k m) Type121.ρM
      (Type121.compat_rho (Type121.data m (by omega))) y) =
    rhoBar300 (parityTorus (Type121.k m) (t121_k_pos hm) y)
  obtain ⟨v, hv⟩ := Torus.exists_ofInt (k := Type121.k m) y
  rw [← hv, matAct_ofInt, parityTorus_ofInt_t121, parityTorus_ofInt_t121]
  have h2 : (2 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r <;> simp [rhoBar300, Type121.ρM, ofCols_mulVec, h2, sub_eq_add_neg,
    ZMod.neg_eq_self_mod_two]

theorem parityTorus_uv_a_t121 {m : ℕ} (hm : 3 ≤ m) :
    parityTorus _ (t121_k_pos hm) ((StrothTypeIndex.t121 m hm).action.φuv Torus.a) =
      Pi.single 1 1 := by
  have h := Type121.data m (by omega)
  change parityTorus (Type121.k m) (t121_k_pos hm) (matAct (Type121.k m)
      (Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m))
      (Type121.compat_uv h) Torus.a) = Pi.single 1 1
  rw [torus_a_eq_ofInt_t121, matAct_ofInt, parityTorus_ofInt_t121]
  have hi := h.hi
  generalize Type120.iV (m + 1) = i at hi ⊢
  generalize Type120.FV (m + 1) = F
  subst hi
  have hvec : Type121.uvM (8 * Type120.GV (m + 1) + 19) F (Type120.GV (m + 1)) (2 ^ m) *ᵥ
      ![0, 1, 0] = ![2 * F * (8 * Type120.GV (m + 1) + 19), -5 * (8 * Type120.GV (m + 1) + 19),
        2 * (8 * Type120.GV (m + 1) + 19) + 2 ^ m] := by
    funext r
    fin_cases r <;> simp [Type121.uvM, Type121.uvA, ofCols_mulVec]
  rw [hvec]
  generalize Type120.GV (m + 1) = G
  have h2 : (2 : ZMod 2) = 0 := by decide
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  have e0 : ((2 * F * (8 * G + 19) : ℤ) : ZMod 2) = 0 := by push_cast; rw [h2]; ring
  have e1 : ((-5 * (8 * G + 19) : ℤ) : ZMod 2) = 1 := by
    rw [show (-5 * (8 * G + 19) : ℤ) = 2 * (-20 * G - 48) + 1 by ring]
    push_cast
    rw [h2]
    ring
  have e2 : ((2 * (8 * G + 19) + 2 ^ (r + 1) : ℤ) : ZMod 2) = 0 := by
    push_cast
    rw [pow_succ, h2]
    ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [e0, e1, e2]
  funext t
  fin_cases t <;> simp [Pi.single_apply]

theorem t121_fixed_rho_t {m : ℕ} (hm : 3 ≤ m) (y : Torus (StrothTypeIndex.t121 m hm).k)
    (hρ : (StrothTypeIndex.t121 m hm).action.φρ y = y)
    (ht : (StrothTypeIndex.t121 m hm).action.φt y = y) : y = 0 := by
  have h := Type121.data m (by omega)
  change matAct (Type121.k m) Type121.ρM (Type121.compat_rho h) y = y at hρ
  change matAct (Type121.k m)
      (Type121.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m))
      (Type121.compat_t h) y = y at ht
  change @Eq (Torus (Type121.k m)) y 0
  obtain ⟨v, hv⟩ := Torus.exists_ofInt (k := Type121.k m) y
  rw [← hv] at hρ ht ⊢
  rw [matAct_ofInt, Torus.ofInt_eq_ofInt_iff] at hρ
  have h1 := (hρ 1).dvd
  have h2 := (hρ 2).dvd
  simp [Type121.ρM, ofCols_mulVec, Type121.k] at h1 h2
  have h3 : 3 * v 2 ≡ 3 * 0 [ZMOD 2 ^ (m + 1)] := by
    rw [Int.modEq_comm, Int.modEq_iff_dvd]
    have := dvd_add h1 h2
    convert this using 1
    ring
  have hv2 : (2 : ℤ) ^ (m + 1) ∣ v 2 := by
    have := (int_modEq_of_mul_three_pow 1 (m + 1) (a := v 2) (b := 0)
      (by rw [pow_one]; exact h3)).symm.dvd
    simpa using this
  have hv1 : (2 : ℤ) ^ (m + 1) ∣ v 1 := by
    have := dvd_sub (dvd_mul_of_dvd_right hv2 2) h2
    convert this using 1
    ring
  have hv' : Torus.ofInt (Type121.k m) v = Torus.ofInt (Type121.k m) ![v 0, 0, 0] := by
    rw [Torus.ofInt_eq_ofInt_iff]
    intro r
    fin_cases r
    · rfl
    · exact (Int.modEq_zero_iff_dvd.mpr (by simpa [Type121.k] using hv1))
    · exact (Int.modEq_zero_iff_dvd.mpr (by simpa [Type121.k] using hv2))
  rw [hv'] at ht ⊢
  rw [matAct_ofInt, Torus.ofInt_eq_ofInt_iff] at ht
  have h4 := (ht 1).dvd
  simp [Type121.tM, ofCols_mulVec, Type121.k] at h4
  have hv0 : (2 : ℤ) ^ m ∣ v 0 := by
    obtain ⟨q, hq⟩ := h4
    refine ⟨q, mul_right_cancel₀ (two_ne_zero (α := ℤ)) ?_⟩
    rw [hq, pow_succ]
    ring
  rw [Torus.ofInt_eq_zero_iff]
  intro r
  fin_cases r
  · simpa [Type121.k] using hv0
  · simp
  · simp

theorem t121_fixed_rho_t_of_mem {S : Type*} [Group S] [Finite S] {B : Subgroup S} {m : ℕ}
    {hm : 3 ≤ m} (D : StrothTypeData B (StrothTypeIndex.t121 m hm)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t121 m hm).action.φρ (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t121 m hm).action.φρ (D.ec y) from
      D.ρ_conj y, hρ]
  have ht' : (StrothTypeIndex.t121 m hm).action.φt (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t121 m hm).action.φt (D.ec y) from
      D.t_conj y, ht]
  exact D.ec_eq_zero_iff.mp (t121_fixed_rho_t hm (D.ec y) hρ' ht')

theorem no_cocycle_index_two_t121 {m : ℕ} (hm : 3 ≤ m) {i F G N K : ℤ}
    (h : Type121.Data m i F G N K) (zuv zt : Torus (Type121.k m))
    (h1 : 2 • zuv = (Type121.action h).φuv Torus.c - Torus.c)
    (h2 : 2 • zt = (Type121.action h).φt Torus.c - Torus.c)
    (h3 : zuv + (Type121.action h).φuv zuv = 0)
    (h4 : zt + (Type121.action h).φt zuv = zuv + (Type121.action h).φuv zt) : False := by
  have hi := h.hi
  have hF := h.hF
  have hN := h.hN
  have hK := h.hK
  have hG := h.hG
  subst hi hF hK
  have hφ : (Type121.action h).φuv = matAct (Type121.k m)
      (Type121.uvM (8 * G + 19) (4 * G + 9) G (2 * K)) (Type121.compat_uv h) := rfl
  have hψ : (Type121.action h).φt = matAct (Type121.k m)
      (Type121.tM (8 * G + 19) (4 * G + 9) G (2 * K)) (Type121.compat_t h) := rfl
  rw [hφ] at h1 h3 h4
  rw [hψ] at h2 h4
  have hk : ∀ r, 1 ≤ Type121.k m r := by
    intro r; fin_cases r <;> simp [Type121.k] <;> omega
  set v₀ : Fin 3 → ℤ := ![-4 * G - 10, 1, -1] with hv₀
  set v₁ : Fin 3 → ℤ := ![-4 * G - 8, 1, 2] with hv₁
  have hw₀ : (2 : ℤ) • (zuv - Torus.ofInt (Type121.k m) v₀) = 0 := by
    rw [smul_sub, two_zsmul, ← two_nsmul, h1, torus_c_eq_ofInt_t121, matAct_ofInt,
      ← Torus.ofInt_zsmul, ← Torus.ofInt_sub, ← Torus.ofInt_sub, Torus.ofInt_eq_zero_iff]
    intro r
    fin_cases r <;> simp [hv₀, Type121.uvM, Type121.uvA, ofCols_mulVec] <;> exact ⟨0, by ring⟩
  have hw₁ : (2 : ℤ) • (zt - Torus.ofInt (Type121.k m) v₁) = 0 := by
    rw [smul_sub, two_zsmul, ← two_nsmul, h2, torus_c_eq_ofInt_t121, matAct_ofInt,
      ← Torus.ofInt_zsmul, ← Torus.ofInt_sub, ← Torus.ofInt_sub, Torus.ofInt_eq_zero_iff]
    intro r
    fin_cases r <;> simp [hv₁, Type121.tM, Type121.uvA, Type121.ρM, ofCols_mulVec] <;>
      exact ⟨0, by ring⟩
  obtain ⟨e, -, he⟩ := (Torus.two_zsmul_eq_zero_iff hk _).mp hw₀
  obtain ⟨f, -, hf⟩ := (Torus.two_zsmul_eq_zero_iff hk _).mp hw₁
  have hK1 : (2 : ℤ) ^ (m - 1) = K := by
    have h2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    linarith
  have hm1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, ← hN]; ring
  have hE : ∀ g : Fin 3 → ℤ, (fun r => g r * 2 ^ (Type121.k m r - 1)) =
      ![g 0 * K, g 1 * (2 * K), g 2 * (2 * K)] := by
    intro g
    funext r
    fin_cases r <;> simp [Type121.k, hK1, ← hN]
  have hzuv : zuv =
      Torus.ofInt (Type121.k m) (v₀ + ![e 0 * K, e 1 * (2 * K), e 2 * (2 * K)]) := by
    rw [Torus.ofInt_add, ← hE, ← he]
    exact (add_sub_cancel _ _).symm
  have hzt : zt = Torus.ofInt (Type121.k m) (v₁ + ![f 0 * K, f 1 * (2 * K), f 2 * (2 * K)]) := by
    rw [Torus.ofInt_add, ← hE, ← hf]
    exact (add_sub_cancel _ _).symm
  rw [hzuv, matAct_ofInt, ← Torus.ofInt_add, Torus.ofInt_eq_zero_iff] at h3
  rw [hzuv, hzt, matAct_ofInt, matAct_ofInt, ← Torus.ofInt_add, ← Torus.ofInt_add,
    Torus.ofInt_eq_ofInt_iff] at h4
  have h32 := h3 2
  have h41 := (h4 1).dvd
  have h42 := (h4 2).dvd
  simp [hv₀, hv₁, Type121.uvM, Type121.uvA, Type121.tM, Type121.ρM, ofCols_mulVec,
    Type121.k] at h32 h41 h42
  rw [hm1] at h32 h41 h42
  obtain ⟨L, hL, hL0⟩ : ∃ L : ℤ, K = 4 * L ∧ L ≠ 0 := ⟨2 ^ (m - 3), by
      rw [← hK1, show m - 1 = (m - 3) + 2 by omega, pow_add]; norm_num; ring, by positivity⟩
  subst hL
  obtain ⟨w1, hw1⟩ := h32
  obtain ⟨w2, hw2⟩ := h41
  obtain ⟨w3, hw3⟩ := h42
  have key : 8 * L * (2 * (3 * (w1 - w2 - w3) - (131072*L^4*e 2 + 1179648*L^4*f 2
      - 18432*L^3*f 2 + 278528*L^3 - 3328*L^2*e 1 - 1280*L^2*e 2 + 768*L^2*f 1
      + 2976*L^2*f 2 - 4608*L^2 + 24*L*e 1 - 24*L*e 2 - 12*L*f 1 - 36*L*f 2 + 520*L + 3*e 0
      - 8*e 1 - 3*e 2 + 3*f 1 + 3*f 2 - 4)) + 1) = 0 := by
    linear_combination (-3) * hw1 + 3 * hw2 + 3 * hw3 + (32768*L^3*e 2 + 294912*L^3*f 2
      + 1536*G*L*e 2 + 13824*G*L*f 2 - 4608*L^2*f 2 + 69632*L^2 - 832*L*e 1 + 3264*L*e 2
      + 192*L*f 1 + 33024*L*f 2 + 3264*G - 1152*L + 7752) * hG
  generalize 3 * (w1 - w2 - w3) - _ = Z at key
  rcases mul_eq_zero.mp key with h0 | h0 <;> omega

theorem no_cocycle_index_four_t121 {m : ℕ} (hm : 3 ≤ m) {i F G N K : ℤ}
    (h : Type121.Data m i F G N K) (z : Torus (Type121.k m))
    (h1 : 2 • z = (Type121.action h).φuv Torus.a - Torus.a)
    (h2 : z + (Type121.action h).φuv z = 0) : False := by
  have hi := h.hi
  have hF := h.hF
  have hN := h.hN
  have hK := h.hK
  have hG := h.hG
  subst hi hF hK
  have hφ : (Type121.action h).φuv = matAct (Type121.k m)
      (Type121.uvM (8 * G + 19) (4 * G + 9) G (2 * K)) (Type121.compat_uv h) := rfl
  rw [hφ] at h1 h2
  have hk : ∀ r, 1 ≤ Type121.k m r := by
    intro r; fin_cases r <;> simp [Type121.k] <;> omega
  set v₀ : Fin 3 → ℤ := ![(4 * G + 9) * (8 * G + 19), -20 * G - 48, 8 * G + 19 + K] with hv₀
  have hw : (2 : ℤ) • (z - Torus.ofInt (Type121.k m) v₀) = 0 := by
    rw [smul_sub, two_zsmul, ← two_nsmul, h1, torus_a_eq_ofInt_t121, matAct_ofInt,
      ← Torus.ofInt_zsmul, ← Torus.ofInt_sub, ← Torus.ofInt_sub, Torus.ofInt_eq_zero_iff]
    intro r
    fin_cases r <;> simp [hv₀, Type121.uvM, Type121.uvA, ofCols_mulVec] <;> exact ⟨0, by ring⟩
  obtain ⟨e, -, he⟩ := (Torus.two_zsmul_eq_zero_iff hk _).mp hw
  have hK1 : (2 : ℤ) ^ (m - 1) = K := by
    have h2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    linarith
  have hm1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, ← hN]; ring
  have hE : (fun r => e r * 2 ^ (Type121.k m r - 1)) =
      ![e 0 * K, e 1 * (2 * K), e 2 * (2 * K)] := by
    funext r
    fin_cases r <;> simp [Type121.k, hK1, ← hN]
  have hz : z = Torus.ofInt (Type121.k m) (v₀ + ![e 0 * K, e 1 * (2 * K), e 2 * (2 * K)]) := by
    rw [Torus.ofInt_add, ← hE, ← he]
    exact (add_sub_cancel _ _).symm
  rw [hz, matAct_ofInt, ← Torus.ofInt_add, Torus.ofInt_eq_zero_iff] at h2
  have h21 := h2 1
  have h22 := h2 2
  simp [hv₀, Type121.uvM, Type121.uvA, Type121.tM, Type121.ρM, ofCols_mulVec,
    Type121.k] at h21 h22
  rw [hm1] at h21 h22
  obtain ⟨L, hL, hL0⟩ : ∃ L : ℤ, K = 4 * L ∧ L ≠ 0 := ⟨2 ^ (m - 3), by
      rw [← hK1, show m - 1 = (m - 3) + 2 by omega, pow_add]; norm_num; ring, by positivity⟩
  subst hL
  obtain ⟨w1, hw1⟩ := h21
  obtain ⟨w2, hw2⟩ := h22
  have key : 8 * L * (2 * (3 * (w1 + w2) - (-25165824*L^5 - 1179648*L^4*e 2 - 196608*L^4
      + 18432*L^3*e 2 - 62464*L^3 - 768*L^2*e 1 - 2976*L^2*e 2 - 592*L^2 + 12*L*e 1
      + 36*L*e 2 + 22*L)) + 1) = 0 := by
    linear_combination (-3) * hw1 + (-3) * hw2 + (-6291456*L^4 - 294912*L^3*e 2
      - 294912*G*L^2 - 49152*L^3 - 13824*G*L*e 2 + 4608*L^2*e 2 - 13824*G^2 - 2304*G*L
      - 703744*L^2 - 192*L*e 1 - 33024*L*e 2 - 65376*G - 5536*L - 77280) * hG
  generalize 3 * (w1 + w2) - _ = Z at key
  rcases mul_eq_zero.mp key with h0 | h0 <;> omega

theorem false_of_index_two_t121_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {m : ℕ} {hm : 3 ≤ m} (D : StrothTypeData B (StrothTypeIndex.t121 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  obtain ⟨zuv, zt, h1, h2, h3, h4⟩ := exists_cocycle_index_two_of_data_Idx4 D (t121_k_pos hm)
    (parityTorus_rho_t121 hm) (fun v h1 h2 => rhoBar300_fixed_check v ⟨h1, h2⟩) hBC hC hrel
    hL hH hcS
  exact no_cocycle_index_two_t121 hm (Type121.data m (by omega)) zuv zt h1 h2 h3 h4

theorem false_of_index_four_t121_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {m : ℕ} {hm : 3 ≤ m} (D : StrothTypeData B (StrothTypeIndex.t121 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  by_cases hcyc : IsCyclic (C ⧸ B.subgroupOf C)
  · obtain ⟨C₂, hBC₂, hC₂C, hrel₂, hL₂⟩ :=
      exists_index_two_of_isCyclic_Idx4 D hBC hC hrel hL hcyc
    exact false_of_index_two_t121_of_data D hBC₂ (hC₂C.trans hC) hrel₂ hL₂ hH (hC₂C.trans hcS)
  · obtain ⟨z, h1, h2⟩ := exists_cocycle_index_four_of_data_Idx4 D (t121_k_pos hm)
      (parityTorus_rho_t121 hm) (fun _ hρ ht => t121_fixed_rho_t_of_mem D hρ ht)
      (parityTorus_uv_a_t121 hm) hBC hC hrel hL hH hcS hcyc
    exact no_cocycle_index_four_t121 hm (Type121.data m (by omega)) z h1 h2

end CFSG.CGT.Stroth77
