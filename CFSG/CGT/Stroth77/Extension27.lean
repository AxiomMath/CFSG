module

public import CFSG.CGT.Stroth77.Extension25Common
public import CFSG.CGT.Stroth77.Extension24Torus

local notation "𝔤" t:max j:max =>
  CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type100.k (t + 1 + 1)) j

local notation "𝔥" t:max j:max =>
  CFSG.CGT.Stroth77.gen
    (CFSG.CGT.Stroth77.StrothTypeIndex.k (CFSG.CGT.Stroth77.StrothTypeIndex.t110 t)) j

public section

namespace CFSG.CGT.Stroth77

theorem t110_k_pos (t : ℕ) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t110 t).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type110.k]

theorem type110_rho_apply_gens (t : ℕ) (i j l : ℤ) :
    (StrothTypeIndex.t110 t).action.φρ (i • (𝔥 t 0) + j • (𝔥 t 1) + l • (𝔥 t 2)) =
      (i - 2 * l) • (𝔥 t 0) + (-l) • (𝔥 t 1) + (j - l) • (𝔥 t 2) := by
  have hc : (StrothTypeIndex.t110 t).action.φρ (𝔥 t 0) = (1 : ℤ) • (𝔥 t 0) := Type110.rho_c t
  have ha : (StrothTypeIndex.t110 t).action.φρ (𝔥 t 1) = (1 : ℤ) • (𝔥 t 2) := Type110.rho_a t
  have hb : (StrothTypeIndex.t110 t).action.φρ (𝔥 t 2) = (-2 : ℤ) • (𝔥 t 0) + (-1 : ℤ) • (𝔥 t 1) +
      (-1 : ℤ) • (𝔥 t 2) := Type110.rho_b t
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hc, ha, hb]
  module

theorem parityTorus_rho110 (t : ℕ) (y : Torus (StrothTypeIndex.t110 t).k) :
    parityTorus _ (t110_k_pos t) ((StrothTypeIndex.t110 t).action.φρ y) =
      rhoBar300 (parityTorus _ (t110_k_pos t) y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t110 t).k y
  rw [type110_rho_apply_gens, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r
  · simp [rhoBar300, h2]
  · simp [rhoBar300, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar300, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_uv_a110 (t : ℕ) :
    parityTorus _ (t110_k_pos t) ((StrothTypeIndex.t110 t).action.φuv Torus.a) =
      Pi.single 1 1 := by
  have h : (StrothTypeIndex.t110 t).action.φuv (𝔥 t 1) =
      (2 : ℤ) • (𝔥 t 0) + (1 : ℤ) • (𝔥 t 1) + (2 : ℤ) • (𝔥 t 2) := Type110.uv_a t
  rw [Torus.a, h, parityTorus_zsmul_gens]
  funext r
  fin_cases r
  · simp [show (2 : ZMod 2) = 0 by decide]
  · simp
  · simp [show (2 : ZMod 2) = 0 by decide]

theorem t110_fixed_rho_t_of_mem {S : Type*} [Group S] [Finite S] {B : Subgroup S} {t : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t110 t)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t110 t).action.φρ (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t110 t).action.φρ (D.ec y) from
      D.ρ_conj y, hρ]
  have ht' : (StrothTypeIndex.t110 t).action.φt (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t110 t).action.φt (D.ec y) from
      D.t_conj y, ht]
  apply D.ec_eq_zero_iff.mp
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t110 t).k (D.ec y)
  rw [hy] at hρ' ht' ⊢
  rw [type110_rho_apply_gens] at hρ'
  obtain ⟨h0, h1, h2⟩ := zsmul_gens_dvd_of_eq hρ'
  change (2 : ℤ) ^ (t + 2) ∣ _ at h0
  change (2 : ℤ) ^ (t + 3) ∣ _ at h1
  change (2 : ℤ) ^ (t + 3) ∣ _ at h2
  have hl : (2 : ℤ) ^ (t + 3) ∣ l := by
    have h4 : (2 : ℤ) ^ (t + 3) ∣ 4 * l := by
      obtain ⟨w, hw⟩ := h0
      refine ⟨w, ?_⟩
      rw [show (4 : ℤ) * l = 2 * (i - (i - 2 * l)) by ring, hw]
      ring
    have h3 : (2 : ℤ) ^ (t + 3) ∣ 3 * l := by
      rw [show (3 : ℤ) * l = (j - -l) + (l - (j - l)) by ring]
      exact dvd_add h1 h2
    rw [show l = 4 * l - 3 * l by ring]
    exact dvd_sub h4 h3
  have hj : (2 : ℤ) ^ (t + 3) ∣ j := by
    rw [show j = (j - -l) - l by ring]
    exact dvd_sub h1 hl
  have hjl : j • (𝔥 t 1) + l • (𝔥 t 2) = 0 := by
    rw [(zsmul_gen_eq_zero 1 j).mpr, (zsmul_gen_eq_zero 2 l).mpr, add_zero]
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd l _).mpr (by exact_mod_cast hl)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd j _).mpr (by exact_mod_cast hj)
  rw [add_assoc, hjl, add_zero] at ht' ⊢
  have htc : (StrothTypeIndex.t110 t).action.φt (𝔥 t 0) =
      (1 : ℤ) • (𝔥 t 0) + (2 : ℤ) • (𝔥 t 1) + (4 * (2 ^ t) : ℤ) • (𝔥 t 2) := Type110.t_c t
  rw [map_zsmul, htc] at ht'
  have h' : i • (𝔥 t 0) + (2 * i) • (𝔥 t 1) + (4 * (2 ^ t) * i) • (𝔥 t 2) =
      i • (𝔥 t 0) + (0 : ℤ) • (𝔥 t 1) + (0 : ℤ) • (𝔥 t 2) := by
    linear_combination (norm := module) ht'
  obtain ⟨-, hi1, -⟩ := zsmul_gens_dvd_of_eq h'
  change (2 : ℤ) ^ (t + 3) ∣ _ at hi1
  have hi : (2 : ℤ) ^ (t + 2) ∣ i := by
    rw [show (0 : ℤ) - 2 * i = 2 * (-i) by ring, show t + 3 = (t + 2) + 1 by ring, pow_succ,
      mul_comm _ (2 : ℤ)] at hi1
    exact dvd_neg.mp ((mul_dvd_mul_iff_left two_ne_zero).mp hi1)
  exact (zsmul_gen_eq_zero 0 i).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd i _).mpr
    (by exact_mod_cast hi))

section Torus

variable (t : ℕ) (V W : Torus (Type100.k (t + 1 + 1)) →+ Torus (Type100.k (t + 1 + 1)))

theorem uv_tor110
    (hVc : V (𝔤 t 0) = (-3 : ℤ) • (𝔤 t 0) + (4 * (2 ^ t) - 2 : ℤ) • (𝔤 t 1) + (-2 : ℤ) • (𝔤 t 2))
    (hVa : V (𝔤 t 1) = (2 : ℤ) • (𝔤 t 0) + (1 : ℤ) • (𝔤 t 1) + (2 : ℤ) • (𝔤 t 2))
    (hVb : V (𝔤 t 2) = (2 - 16 * (2 ^ t) : ℤ) • (𝔤 t 0) + (2 - 8 * (2 ^ t) : ℤ) • (𝔤 t 1) +
      (1 - 8 * (2 ^ t) : ℤ) • (𝔤 t 2))
    (x y z : ℤ) : V (tor300 (t + 1) x y z) = tor300 (t + 1) x (x + y) (x + z) := by
  have e : tor300 (t + 1) x y z = (x * 2 ^ (t + 1)) • (𝔤 t 0) +
      (y * 2 ^ (t + 1 + 1)) • (𝔤 t 1) + (z * 2 ^ (t + 1 + 1)) • (𝔤 t 2) := rfl
  have hexact : V (tor300 (t + 1) x y z) =
      tor300 (t + 1) (-3 * x + 4 * y + z * (4 - 32 * (2 ^ t)))
        (x * (2 * (2 ^ t) - 1) + y + z * (2 - 8 * (2 ^ t)))
        (-x + 2 * y + z * (1 - 8 * (2 ^ t))) := by
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hVc, hVa, hVb]
    simp only [tor300]
    module
  rw [hexact]
  apply tor300_congr
  · exact ⟨2 * x - 2 * y - z * (2 - 16 * (2 ^ t)), by ring⟩
  · exact ⟨x * (1 - (2 ^ t)) - z * (1 - 4 * (2 ^ t)), by ring⟩
  · exact ⟨x - y + 4 * z * (2 ^ t), by ring⟩

theorem t_tor110
    (hWc : W (𝔤 t 0) = (1 : ℤ) • (𝔤 t 0) + (2 : ℤ) • (𝔤 t 1) + (4 * (2 ^ t) : ℤ) • (𝔤 t 2))
    (hWa : W (𝔤 t 1) = (-1 : ℤ) • (𝔤 t 1))
    (hWb : W (𝔤 t 2) = (-2 : ℤ) • (𝔤 t 0) + (-2 : ℤ) • (𝔤 t 1) + (-1 : ℤ) • (𝔤 t 2))
    (x y z : ℤ) : W (tor300 (t + 1) x y z) = tor300 (t + 1) x (x + y) z := by
  have e : tor300 (t + 1) x y z = (x * 2 ^ (t + 1)) • (𝔤 t 0) +
      (y * 2 ^ (t + 1 + 1)) • (𝔤 t 1) + (z * 2 ^ (t + 1 + 1)) • (𝔤 t 2) := rfl
  have hexact : W (tor300 (t + 1) x y z) =
      tor300 (t + 1) (x - 4 * z) (x - y - 2 * z) (2 * x * (2 ^ t) - z) := by
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hWc, hWa, hWb]
    simp only [tor300]
    module
  rw [hexact]
  apply tor300_congr
  · exact ⟨2 * z, by ring⟩
  · exact ⟨y + z, by ring⟩
  · exact ⟨z - x * (2 ^ t), by ring⟩

theorem no_cocycle_index_two_t110
    (hVc : V (𝔤 t 0) = (-3 : ℤ) • (𝔤 t 0) + (4 * (2 ^ t) - 2 : ℤ) • (𝔤 t 1) + (-2 : ℤ) • (𝔤 t 2))
    (hVa : V (𝔤 t 1) = (2 : ℤ) • (𝔤 t 0) + (1 : ℤ) • (𝔤 t 1) + (2 : ℤ) • (𝔤 t 2))
    (hVb : V (𝔤 t 2) = (2 - 16 * (2 ^ t) : ℤ) • (𝔤 t 0) + (2 - 8 * (2 ^ t) : ℤ) • (𝔤 t 1) +
      (1 - 8 * (2 ^ t) : ℤ) • (𝔤 t 2))
    (hWc : W (𝔤 t 0) = (1 : ℤ) • (𝔤 t 0) + (2 : ℤ) • (𝔤 t 1) + (4 * (2 ^ t) : ℤ) • (𝔤 t 2))
    (hWa : W (𝔤 t 1) = (-1 : ℤ) • (𝔤 t 1))
    (hWb : W (𝔤 t 2) = (-2 : ℤ) • (𝔤 t 0) + (-2 : ℤ) • (𝔤 t 1) + (-1 : ℤ) • (𝔤 t 2))
    (zuv zt : Torus (Type100.k (t + 1 + 1)))
    (h1 : 2 • zuv = V (𝔤 t 0) - (𝔤 t 0)) (h2 : 2 • zt = W (𝔤 t 0) - (𝔤 t 0))
    (h3 : zuv + V zuv = 0) (h4 : zt + W zuv = zuv + V zt) : False := by
  have hVt := uv_tor110 t V hVc hVa hVb
  have hWt := t_tor110 t W hWc hWa hWb
  obtain ⟨x0, x1, x2, hx⟩ := exists_tor300 (s := t + 1)
    (w := zuv - ((-2 : ℤ) • (𝔤 t 0) + (2 * (2 ^ t) - 1 : ℤ) • (𝔤 t 1) + (-1 : ℤ) • (𝔤 t 2)))
    (by rw [smul_sub, two_zsmul, ← two_nsmul, h1, hVc]; module)
  obtain ⟨y0, y1, y2, hy⟩ := exists_tor300 (s := t + 1)
    (w := zt - ((𝔤 t 1) + (2 * (2 ^ t) : ℤ) • (𝔤 t 2)))
    (by rw [smul_sub, two_zsmul, ← two_nsmul, h2, hWc]; module)
  have hzuv : zuv = (-2 : ℤ) • (𝔤 t 0) + (2 * (2 ^ t) - 1 : ℤ) • (𝔤 t 1) + (-1 : ℤ) • (𝔤 t 2) +
      tor300 (t + 1) x0 x1 x2 := by
    rw [← hx]; abel
  have hzt : zt = (𝔤 t 1) + (2 * (2 ^ t) : ℤ) • (𝔤 t 2) + tor300 (t + 1) y0 y1 y2 := by
    rw [← hy]; abel
  have hodd : 2 ∣ x0 + 1 := by
    rw [hzuv] at h3
    simp only [map_add, map_zsmul, hVc, hVa, hVb, hVt] at h3
    have key : tor300 (t + 1) (10 + x0 + x0) (1 + x1 + (x0 + x1)) (3 + x2 + (x0 + x2)) =
        tor300 (t + 1) 0 0 0 := by
      simp only [tor300] at h3 ⊢
      linear_combination (norm := module) h3
    rw [tor300_eq_iff] at key
    omega
  have heven : 2 ∣ x0 := by
    rw [hzuv, hzt] at h4
    simp only [map_add, map_zsmul, hVc, hVa, hVb, hWc, hWa, hWb, hVt, hWt] at h4
    have key : tor300 (t + 1) (-2 + 16 * (2 ^ t) + y0 + x0) (-2 + 4 * (2 ^ t) + y1 + (x0 + x1))
        (-2 + 4 * (2 ^ t) + y2 + x2) =
        tor300 (t + 1) (x0 + y0) (x1 + (y0 + y1)) (x2 + (y0 + y2)) := by
      simp only [tor300] at h4 ⊢
      linear_combination (norm := module) h4
    rw [tor300_eq_iff] at key
    omega
  omega

theorem no_cocycle_index_four_t110
    (hVc : V (𝔤 t 0) = (-3 : ℤ) • (𝔤 t 0) + (4 * (2 ^ t) - 2 : ℤ) • (𝔤 t 1) + (-2 : ℤ) • (𝔤 t 2))
    (hVa : V (𝔤 t 1) = (2 : ℤ) • (𝔤 t 0) + (1 : ℤ) • (𝔤 t 1) + (2 : ℤ) • (𝔤 t 2))
    (hVb : V (𝔤 t 2) = (2 - 16 * (2 ^ t) : ℤ) • (𝔤 t 0) + (2 - 8 * (2 ^ t) : ℤ) • (𝔤 t 1) +
      (1 - 8 * (2 ^ t) : ℤ) • (𝔤 t 2))
    (z : Torus (Type100.k (t + 1 + 1))) (h1 : 2 • z = V (𝔤 t 1) - (𝔤 t 1)) (h2 : z + V z = 0) :
    False := by
  have hVt := uv_tor110 t V hVc hVa hVb
  obtain ⟨x0, x1, x2, hx⟩ := exists_tor300 (s := t + 1) (w := z - ((𝔤 t 0) + (𝔤 t 2)))
    (by rw [smul_sub, two_zsmul, ← two_nsmul, h1, hVa]; module)
  have hz : z = (𝔤 t 0) + (𝔤 t 2) + tor300 (t + 1) x0 x1 x2 := by rw [← hx]; abel
  rw [hz] at h2
  simp only [map_add, map_zsmul, hVc, hVa, hVb, hVt] at h2
  have key : tor300 (t + 1) (-8 + x0 + x0) (-1 + x1 + (x0 + x1)) (-2 + x2 + (x0 + x2)) =
      tor300 (t + 1) 0 0 0 := by
    simp only [tor300] at h2 ⊢
    linear_combination (norm := module) h2
  rw [tor300_eq_iff] at key
  omega

end Torus

theorem false_of_index_two_t110_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {t : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t110 t))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  obtain ⟨zuv, zt, h1, h2, h3, h4⟩ := exists_cocycle_index_two_of_data_Idx4 D (t110_k_pos t)
    (parityTorus_rho110 t) (fun v h1 h2 => rhoBar300_fixed_check v ⟨h1, h2⟩) hBC hC hrel hL hH hcS
  exact no_cocycle_index_two_t110 t (StrothTypeIndex.t110 t).action.φuv
    (StrothTypeIndex.t110 t).action.φt (Type110.uv_c t) (Type110.uv_a t) (Type110.uv_b t)
    (Type110.t_c t) (Type110.t_a t) (Type110.t_b t) zuv zt h1 h2 h3 h4

theorem false_of_index_four_t110_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {t : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t110 t))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  by_cases hcyc : IsCyclic (C ⧸ B.subgroupOf C)
  · obtain ⟨C₂, hBC₂, hC₂C, hrel₂, hL₂⟩ :=
      exists_index_two_of_isCyclic_Idx4 D hBC hC hrel hL hcyc
    exact false_of_index_two_t110_of_data D hBC₂ (hC₂C.trans hC) hrel₂ hL₂ hH (hC₂C.trans hcS)
  · obtain ⟨z, h1, h2⟩ := exists_cocycle_index_four_of_data_Idx4 D (t110_k_pos t)
      (parityTorus_rho110 t) (fun _ hρ ht => t110_fixed_rho_t_of_mem D hρ ht)
      (parityTorus_uv_a110 t) hBC hC hrel hL hH hcS hcyc
    exact no_cocycle_index_four_t110 t (StrothTypeIndex.t110 t).action.φuv
      (Type110.uv_c t) (Type110.uv_a t) (Type110.uv_b t) z h1 h2

end CFSG.CGT.Stroth77
