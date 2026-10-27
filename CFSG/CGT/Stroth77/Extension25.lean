module

public import CFSG.CGT.Stroth77.Extension25Common
public import CFSG.CGT.Stroth77.Extension24Torus

local notation "𝔤" s:max j:max => CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type100.k (s + 1)) j

local notation "𝔥" s:max j:max =>
  CFSG.CGT.Stroth77.gen
    (CFSG.CGT.Stroth77.StrothTypeIndex.k (CFSG.CGT.Stroth77.StrothTypeIndex.t101 s)) j

public section

namespace CFSG.CGT.Stroth77

theorem t101_k_pos (s : ℕ) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t101 s).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type101.k]

theorem type101_rho_apply_gens (s : ℕ) (i j l : ℤ) :
    (StrothTypeIndex.t101 s).action.φρ (i • (𝔥 s 0) + j • (𝔥 s 1) + l • (𝔥 s 2)) =
      (i - 2 * l) • (𝔥 s 0) + (-l) • (𝔥 s 1) + (j - l) • (𝔥 s 2) := by
  have hc : (StrothTypeIndex.t101 s).action.φρ (𝔥 s 0) = (1 : ℤ) • (𝔥 s 0) := Type101.rho_c s
  have ha : (StrothTypeIndex.t101 s).action.φρ (𝔥 s 1) = (1 : ℤ) • (𝔥 s 2) := Type101.rho_a s
  have hb : (StrothTypeIndex.t101 s).action.φρ (𝔥 s 2) = (-2 : ℤ) • (𝔥 s 0) + (-1 : ℤ) • (𝔥 s 1) +
      (-1 : ℤ) • (𝔥 s 2) := Type101.rho_b s
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hc, ha, hb]
  module

theorem parityTorus_rho101 (s : ℕ) (y : Torus (StrothTypeIndex.t101 s).k) :
    parityTorus _ (t101_k_pos s) ((StrothTypeIndex.t101 s).action.φρ y) =
      rhoBar300 (parityTorus _ (t101_k_pos s) y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t101 s).k y
  rw [type101_rho_apply_gens, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  funext t
  fin_cases t
  · simp [rhoBar300, h2]
  · simp [rhoBar300, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar300, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_uv_a101 (s : ℕ) :
    parityTorus _ (t101_k_pos s) ((StrothTypeIndex.t101 s).action.φuv Torus.a) =
      Pi.single 1 1 := by
  have h : (StrothTypeIndex.t101 s).action.φuv (𝔥 s 1) =
      (2 : ℤ) • (𝔥 s 0) + (1 : ℤ) • (𝔥 s 1) + (2 * (2 ^ s) + 2 : ℤ) • (𝔥 s 2) := Type101.uv_a s
  rw [Torus.a, h, parityTorus_zsmul_gens]
  have e1 : ((2 * (2 ^ s) + 2 : ℤ) : ZMod 2) = 0 := by
    push_cast
    rw [show (2 : ZMod 2) = 0 by decide]
    ring
  funext t
  fin_cases t
  · simp [show (2 : ZMod 2) = 0 by decide]
  · simp
  · simpa using e1

theorem t101_fixed_rho_t_of_mem {S : Type*} [Group S] [Finite S] {B : Subgroup S} {s : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t101 s)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t101 s).action.φρ (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t101 s).action.φρ (D.ec y) from
      D.ρ_conj y, hρ]
  have ht' : (StrothTypeIndex.t101 s).action.φt (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t101 s).action.φt (D.ec y) from
      D.t_conj y, ht]
  apply D.ec_eq_zero_iff.mp
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t101 s).k (D.ec y)
  rw [hy] at hρ' ht' ⊢
  rw [type101_rho_apply_gens] at hρ'
  obtain ⟨h0, h1, h2⟩ := zsmul_gens_dvd_of_eq hρ'
  change (2 : ℤ) ^ (s + 1) ∣ _ at h0
  change (2 : ℤ) ^ (s + 2) ∣ _ at h1
  change (2 : ℤ) ^ (s + 2) ∣ _ at h2
  have hl : (2 : ℤ) ^ (s + 2) ∣ l := by
    have h4 : (2 : ℤ) ^ (s + 2) ∣ 4 * l := by
      obtain ⟨w, hw⟩ := h0
      refine ⟨w, ?_⟩
      rw [show (4 : ℤ) * l = 2 * (i - (i - 2 * l)) by ring, hw]
      ring
    have h3 : (2 : ℤ) ^ (s + 2) ∣ 3 * l := by
      rw [show (3 : ℤ) * l = (j - -l) + (l - (j - l)) by ring]
      exact dvd_add h1 h2
    rw [show l = 4 * l - 3 * l by ring]
    exact dvd_sub h4 h3
  have hj : (2 : ℤ) ^ (s + 2) ∣ j := by
    rw [show j = (j - -l) - l by ring]
    exact dvd_sub h1 hl
  have hjl : j • (𝔥 s 1) + l • (𝔥 s 2) = 0 := by
    rw [(zsmul_gen_eq_zero 1 j).mpr, (zsmul_gen_eq_zero 2 l).mpr, add_zero]
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd l _).mpr (by exact_mod_cast hl)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd j _).mpr (by exact_mod_cast hj)
  rw [add_assoc, hjl, add_zero] at ht' ⊢
  have htc : (StrothTypeIndex.t101 s).action.φt (𝔥 s 0) = (1 : ℤ) • (𝔥 s 0) + (2 : ℤ) • (𝔥 s 1) :=
    Type101.t_c s
  rw [map_zsmul, htc] at ht'
  have h' : i • (𝔥 s 0) + (2 * i) • (𝔥 s 1) + (0 : ℤ) • (𝔥 s 2) =
      i • (𝔥 s 0) + (0 : ℤ) • (𝔥 s 1) + (0 : ℤ) • (𝔥 s 2) := by
    linear_combination (norm := module) ht'
  obtain ⟨-, hi1, -⟩ := zsmul_gens_dvd_of_eq h'
  change (2 : ℤ) ^ (s + 2) ∣ _ at hi1
  have hi : (2 : ℤ) ^ (s + 1) ∣ i := by
    rw [show (0 : ℤ) - 2 * i = 2 * (-i) by ring, show s + 2 = (s + 1) + 1 by ring, pow_succ,
      mul_comm _ (2 : ℤ)] at hi1
    exact dvd_neg.mp ((mul_dvd_mul_iff_left two_ne_zero).mp hi1)
  exact (zsmul_gen_eq_zero 0 i).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd i _).mpr
    (by exact_mod_cast hi))

section Torus

variable (s : ℕ) (V W : Torus (Type100.k (s + 1)) →+ Torus (Type100.k (s + 1)))

theorem uv_tor101
    (hVc : V (𝔤 s 0) = (-3 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) + (-2 : ℤ) • (𝔤 s 2))
    (hVa : V (𝔤 s 1) = (2 : ℤ) • (𝔤 s 0) + (1 : ℤ) • (𝔤 s 1) + (2 * (2 ^ s) + 2 : ℤ) • (𝔤 s 2))
    (hVb : V (𝔤 s 2) = (2 : ℤ) • (𝔤 s 0) + (4 * (2 ^ s) ^ 2 + 6 * (2 ^ s) + 2 : ℤ) • (𝔤 s 1) +
      (1 : ℤ) • (𝔤 s 2))
    (x y z : ℤ) : V (tor300 s x y z) = tor300 s x (x + y) (x + z) := by
  have e : tor300 s x y z =
      (x * 2 ^ s) • (𝔤 s 0) + (y * 2 ^ (s + 1)) • (𝔤 s 1) + (z * 2 ^ (s + 1)) • (𝔤 s 2) := rfl
  have hexact : V (tor300 s x y z) =
      tor300 s (-3 * x + 4 * y + 4 * z) (-x + y + z * (4 * (2 ^ s) ^ 2 + 6 * (2 ^ s) + 2))
        (-x + y * (2 * (2 ^ s) + 2) + z) := by
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hVc, hVa, hVb]
    simp only [tor300]
    module
  rw [hexact]
  apply tor300_congr
  · exact ⟨2 * x - 2 * y - 2 * z, by ring⟩
  · exact ⟨x - z * (2 * (2 ^ s) ^ 2 + 3 * (2 ^ s) + 1), by ring⟩
  · exact ⟨x - y * ((2 ^ s) + 1), by ring⟩

theorem t_tor101 (hWc : W (𝔤 s 0) = (1 : ℤ) • (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1))
    (hWa : W (𝔤 s 1) = (2 * (2 ^ s) - 1 : ℤ) • (𝔤 s 1))
    (hWb : W (𝔤 s 2) = (-4 * (2 ^ s) - 2 : ℤ) • (𝔤 s 0) + (-2 * (2 ^ s) - 2 : ℤ) • (𝔤 s 1) +
      (-2 * (2 ^ s) - 1 : ℤ) • (𝔤 s 2))
    (x y z : ℤ) : W (tor300 s x y z) = tor300 s x (x + y) z := by
  have e : tor300 s x y z =
      (x * 2 ^ s) • (𝔤 s 0) + (y * 2 ^ (s + 1)) • (𝔤 s 1) + (z * 2 ^ (s + 1)) • (𝔤 s 2) := rfl
  have hexact : W (tor300 s x y z) =
      tor300 s (x + z * (-8 * (2 ^ s) - 4)) (x + y * (2 * (2 ^ s) - 1) + z * (-2 * (2 ^ s) - 2))
        (z * (-2 * (2 ^ s) - 1)) := by
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hWc, hWa, hWb]
    simp only [tor300]
    module
  rw [hexact]
  apply tor300_congr
  · exact ⟨z * (4 * (2 ^ s) + 2), by ring⟩
  · exact ⟨y * (1 - (2 ^ s)) + z * ((2 ^ s) + 1), by ring⟩
  · exact ⟨z * ((2 ^ s) + 1), by ring⟩

theorem no_cocycle_index_two_t101
    (hVc : V (𝔤 s 0) = (-3 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) + (-2 : ℤ) • (𝔤 s 2))
    (hVa : V (𝔤 s 1) = (2 : ℤ) • (𝔤 s 0) + (1 : ℤ) • (𝔤 s 1) + (2 * (2 ^ s) + 2 : ℤ) • (𝔤 s 2))
    (hVb : V (𝔤 s 2) = (2 : ℤ) • (𝔤 s 0) + (4 * (2 ^ s) ^ 2 + 6 * (2 ^ s) + 2 : ℤ) • (𝔤 s 1) +
      (1 : ℤ) • (𝔤 s 2))
    (hWc : W (𝔤 s 0) = (1 : ℤ) • (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1))
    (hWa : W (𝔤 s 1) = (2 * (2 ^ s) - 1 : ℤ) • (𝔤 s 1))
    (hWb : W (𝔤 s 2) = (-4 * (2 ^ s) - 2 : ℤ) • (𝔤 s 0) + (-2 * (2 ^ s) - 2 : ℤ) • (𝔤 s 1) +
      (-2 * (2 ^ s) - 1 : ℤ) • (𝔤 s 2))
    (zuv zt : Torus (Type100.k (s + 1)))
    (h1 : 2 • zuv = V (𝔤 s 0) - (𝔤 s 0)) (h2 : 2 • zt = W (𝔤 s 0) - (𝔤 s 0))
    (h3 : zuv + V zuv = 0) (h4 : zt + W zuv = zuv + V zt) : False := by
  have hVt := uv_tor101 s V hVc hVa hVb
  have hWt := t_tor101 s W hWc hWa hWb
  obtain ⟨x0, x1, x2, hx⟩ := exists_tor300 (s := s)
    (w := zuv - ((-2 : ℤ) • (𝔤 s 0) + (-1 : ℤ) • (𝔤 s 1) + (-1 : ℤ) • (𝔤 s 2)))
    (by rw [smul_sub, two_zsmul, ← two_nsmul, h1, hVc]; module)
  obtain ⟨y0, y1, y2, hy⟩ := exists_tor300 (s := s) (w := zt - (𝔤 s 1))
    (by rw [smul_sub, two_zsmul, ← two_nsmul, h2, hWc]; module)
  have hzuv : zuv =
      (-2 : ℤ) • (𝔤 s 0) + (-1 : ℤ) • (𝔤 s 1) + (-1 : ℤ) • (𝔤 s 2) + tor300 s x0 x1 x2 := by
    rw [← hx]; abel
  have hzt : zt = (𝔤 s 1) + tor300 s y0 y1 y2 := by rw [← hy]; abel
  have hodd : 2 ∣ x0 + 1 := by
    rw [hzuv] at h3
    simp only [map_add, map_zsmul, hVc, hVa, hVb, hVt] at h3
    have key : tor300 s (x0 + x0) (-2 * (2 ^ s) - 3 + x1 + (x0 + x1)) (-1 + x2 + (x0 + x2)) =
        tor300 s 0 0 0 := by
      simp only [tor300] at h3 ⊢
      linear_combination (norm := module) h3
    rw [tor300_eq_iff] at key
    omega
  have heven : 2 ∣ x0 := by
    rw [hzuv, hzt] at h4
    simp only [map_add, map_zsmul, hVc, hVa, hVb, hWc, hWa, hWb, hVt, hWt] at h4
    have key : tor300 s (4 + y0 + x0) (y1 + (x0 + x1)) (y2 + x2) =
        tor300 s (x0 + y0) (x1 + (y0 + y1)) (x2 + (y0 + y2)) := by
      simp only [tor300] at h4 ⊢
      linear_combination (norm := module) h4
    rw [tor300_eq_iff] at key
    omega
  omega

theorem no_cocycle_index_four_t101 (hs : 1 ≤ s)
    (hVc : V (𝔤 s 0) = (-3 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) + (-2 : ℤ) • (𝔤 s 2))
    (hVa : V (𝔤 s 1) = (2 : ℤ) • (𝔤 s 0) + (1 : ℤ) • (𝔤 s 1) + (2 * (2 ^ s) + 2 : ℤ) • (𝔤 s 2))
    (hVb : V (𝔤 s 2) = (2 : ℤ) • (𝔤 s 0) + (4 * (2 ^ s) ^ 2 + 6 * (2 ^ s) + 2 : ℤ) • (𝔤 s 1) +
      (1 : ℤ) • (𝔤 s 2))
    (z : Torus (Type100.k (s + 1))) (h1 : 2 • z = V (𝔤 s 1) - (𝔤 s 1)) (h2 : z + V z = 0) :
    False := by
  have hVt := uv_tor101 s V hVc hVa hVb
  obtain ⟨x0, x1, x2, hx⟩ := exists_tor300 (s := s)
    (w := z - ((𝔤 s 0) + (1 + 2 ^ s : ℤ) • (𝔤 s 2)))
    (by rw [smul_sub, two_zsmul, ← two_nsmul, h1, hVa]; module)
  have hz : z = (𝔤 s 0) + (1 + 2 ^ s : ℤ) • (𝔤 s 2) + tor300 s x0 x1 x2 := by
    rw [← hx]; abel
  rw [hz] at h2
  simp only [map_add, map_zsmul, hVc, hVa, hVb, hVt] at h2
  have key : tor300 s (2 + x0 + x0) (2 * (2 ^ s) ^ 2 + 5 * (2 ^ s) + 4 + x1 + (x0 + x1))
      (1 + x2 + (x0 + x2)) = tor300 s 0 0 0 := by
    simp only [tor300] at h2 ⊢
    linear_combination (norm := module) h2
  rw [tor300_eq_iff] at key
  have h2s : (2 : ℤ) ∣ 2 ^ s := by
    obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
    exact ⟨2 ^ r, by ring⟩
  omega

end Torus

theorem false_of_index_two_t101_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {s : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t101 s))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  obtain ⟨zuv, zt, h1, h2, h3, h4⟩ := exists_cocycle_index_two_of_data_Idx4 D (t101_k_pos s)
    (parityTorus_rho101 s) (fun v h1 h2 => rhoBar300_fixed_check v ⟨h1, h2⟩) hBC hC hrel hL hH hcS
  exact no_cocycle_index_two_t101 s (StrothTypeIndex.t101 s).action.φuv
    (StrothTypeIndex.t101 s).action.φt (Type101.uv_c s) (Type101.uv_a s) (Type101.uv_b s)
    (Type101.t_c s) (Type101.t_a s) (Type101.t_b s) zuv zt h1 h2 h3 h4

theorem false_of_index_four_t101_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {s : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t101 s)) (hs : 1 ≤ s)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  by_cases hcyc : IsCyclic (C ⧸ B.subgroupOf C)
  · obtain ⟨C₂, hBC₂, hC₂C, hrel₂, hL₂⟩ :=
      exists_index_two_of_isCyclic_Idx4 D hBC hC hrel hL hcyc
    exact false_of_index_two_t101_of_data D hBC₂ (hC₂C.trans hC) hrel₂ hL₂ hH (hC₂C.trans hcS)
  · obtain ⟨z, h1, h2⟩ := exists_cocycle_index_four_of_data_Idx4 D (t101_k_pos s)
      (parityTorus_rho101 s) (fun _ hρ ht => t101_fixed_rho_t_of_mem D hρ ht)
      (parityTorus_uv_a101 s) hBC hC hrel hL hH hcS hcyc
    exact no_cocycle_index_four_t101 s (StrothTypeIndex.t101 s).action.φuv hs
      (Type101.uv_c s) (Type101.uv_a s) (Type101.uv_b s) z h1 h2

end CFSG.CGT.Stroth77
