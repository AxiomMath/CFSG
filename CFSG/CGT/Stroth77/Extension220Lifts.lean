module

public import CFSG.CGT.Stroth77.Extension220Torus

local notation "𝔤" s:max j:max => CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type230.k s) j

public section

namespace CFSG.CGT.Stroth77

namespace Ext220

open Matrix Ext218

variable {s : ℕ} {i F G : ℤ}

theorem rho_uv_rel220 {A : Type*} [AddCommGroup A] {V W U R : A →+ A}
    (hrels : SigmaFourRels V W U R) (x : A) :
    R (V (R (R x))) = V (R (R (V (R x)))) := by
  have huvρ : ∀ y, R (V y) = W (R y) := fun y => DFunLike.congr_fun hrels.uv_rho y
  have htρ : ∀ y, R (W y) = W (V (R y)) := fun y => DFunLike.congr_fun hrels.t_rho y
  have hR3 : ∀ y, R (R (R y)) = y := fun y => DFunLike.congr_fun hrels.rho_cube y
  have hW : ∀ y, W y = R (V (R (R y))) := fun y => by rw [huvρ, hR3]
  calc R (V (R (R x))) = W x := (hW x).symm
    _ = R (R (R (W x))) := (hR3 _).symm
    _ = R (R (W (V (R x)))) := by rw [htρ]
    _ = R (R (R (V (R (R (V (R x))))))) := by rw [hW (V (R x))]
    _ = V (R (R (V (R x)))) := hR3 _

section Relations

variable (h : Type230.Data s i F G) {V U : Torus (Type230.k s) →+ Torus (Type230.k s)}
  {u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 : ℤ}

theorem lift_uv_sq_e_t131 (hV0 : V (𝔤 s 0) = (Type230.action h).φuv (𝔤 s 0))
    (hV1 : V (𝔤 s 1) = (Type230.action h).φuv (𝔤 s 1) + tor230 s v0 v1 v2)
    (hV2 : V (𝔤 s 2) = (Type230.action h).φuv (𝔤 s 2) + tor230 s v3 v4 v5)
    (hVV : V (V (𝔤 s 1)) = 𝔤 s 1) : 2 ∣ v0 := by
  obtain ⟨p, Q, R, hA⟩ := uv_gen1_par_t230 h
  have e := hVV
  rw [hV1, map_add, dev_tor230 V _ hV0 hV1 hV2, phiUV_tor230 h, hA,
    dev_apply220 V _ hV0 hV1 hV2, ← hA, SigmaFourAction.φuv_φuv, odd_zsmul_tor230,
    even_zsmul_tor230] at e
  simp only [add_zero] at e
  have e' : tor230 s (v0 + v0) (v1 + (v0 + v1)) (v2 + (v0 + v2)) = tor230 s 0 0 0 := by
    rw [← tor230_add, tor230_zero]
    linear_combination (norm := module) e
  rw [tor230_eq_iff] at e'
  clear * - e'
  omega

theorem lift_uv_sq_f_t131 (hV0 : V (𝔤 s 0) = (Type230.action h).φuv (𝔤 s 0))
    (hV1 : V (𝔤 s 1) = (Type230.action h).φuv (𝔤 s 1) + tor230 s v0 v1 v2)
    (hV2 : V (𝔤 s 2) = (Type230.action h).φuv (𝔤 s 2) + tor230 s v3 v4 v5)
    (hVV : V (V (𝔤 s 2)) = 𝔤 s 2) : 2 ∣ v3 := by
  obtain ⟨p, Q, R, hA⟩ := uv_gen2_par_t230 h
  have e := hVV
  rw [hV2, map_add, dev_tor230 V _ hV0 hV1 hV2, phiUV_tor230 h, hA,
    dev_apply220 V _ hV0 hV1 hV2, ← hA, SigmaFourAction.φuv_φuv, odd_zsmul_tor230,
    even_zsmul_tor230] at e
  simp only [add_zero] at e
  have e' : tor230 s (v3 + v3) (v4 + (v3 + v4)) (v5 + (v3 + v5)) = tor230 s 0 0 0 := by
    rw [← tor230_add, tor230_zero]
    linear_combination (norm := module) e
  rw [tor230_eq_iff] at e'
  clear * - e'
  omega

theorem lift_u_sq_t131 (hU0 : U (𝔤 s 0) = (Type230.action h).φu (𝔤 s 0))
    (hU1 : U (𝔤 s 1) = (Type230.action h).φu (𝔤 s 1) + tor230 s u0 u1 u2)
    (hU2 : U (𝔤 s 2) = (Type230.action h).φu (𝔤 s 2) + tor230 s u3 u4 u5)
    (hUU : U (U (𝔤 s 1)) = 𝔤 s 1) : 2 ∣ u3 + u0 ∧ 2 ∣ u4 + u2 ∧ 2 ∣ u5 + u1 := by
  obtain ⟨p, Q, R, hA⟩ := u_gen1_par_t230 h
  have e := hUU
  rw [hU1, map_add, dev_tor230 U _ hU0 hU1 hU2, phiU_tor230 h, hA,
    dev_apply220 U _ hU0 hU1 hU2, ← hA, SigmaFourAction.φu_φu, odd_zsmul_tor230,
    even_zsmul_tor230] at e
  simp only [add_zero] at e
  have e' : tor230 s (u3 + u0) (u4 + u2) (u5 + u1) = tor230 s 0 0 0 := by
    rw [← tor230_add, tor230_zero]
    linear_combination (norm := module) e
  rw [tor230_eq_iff] at e'
  clear * - e'
  omega

theorem lift_u_rho_t131 (hU0 : U (𝔤 s 0) = (Type230.action h).φu (𝔤 s 0))
    (hU1 : U (𝔤 s 1) = (Type230.action h).φu (𝔤 s 1) + tor230 s u0 u1 u2)
    (hU2 : U (𝔤 s 2) = (Type230.action h).φu (𝔤 s 2) + tor230 s u3 u4 u5)
    (hUR : (Type230.action h).φρ (U ((Type230.action h).φρ (U (𝔤 s 1)))) = 𝔤 s 1) :
    2 ∣ u3 ∧ 2 ∣ u5 ∧ 2 ∣ u2 + u4 + u5 := by
  obtain ⟨p, Q, R, hA⟩ := u_gen1_par_t230 h
  have hRt := phiR_tor230 h
  have hRA : (Type230.action h).φρ ((Type230.action h).φu (𝔤 s 1)) =
      (p - (2 * R + 1)) • 𝔤 s 0 + (2 * (-R - 1) + 1) • 𝔤 s 1 +
        (2 * (Q - R - 1) + 1) • 𝔤 s 2 := by
    rw [hA, phiR_apply_gens_t230 h]
    module
  have L : (Type230.action h).φρ (U ((Type230.action h).φρ (U (𝔤 s 1)))) = 𝔤 s 1 +
      tor230 s u0 u2 (u1 + u2) + tor230 s u3 u5 (u4 + u5) + tor230 s u0 u2 (u1 + u2 + u2) := by
    rw [hU1, map_add (Type230.action h).φρ, hRt, map_add U, dev_tor230 U _ hU0 hU1 hU2,
      phiU_tor230 h, hRA, dev_apply220 U _ hU0 hU1 hU2, ← hRA, odd_zsmul_tor230,
      odd_zsmul_tor230, map_add (Type230.action h).φρ, map_add (Type230.action h).φρ,
      map_add (Type230.action h).φρ, SigmaFourAction.φρ_φu_φρ_φu, hRt, hRt, hRt]
  have e := hUR
  rw [L] at e
  have e' : tor230 s (u0 + u3 + u0) (u2 + u5 + u2) ((u1 + u2) + (u4 + u5) + (u1 + u2 + u2)) =
      tor230 s 0 0 0 := by
    rw [← tor230_add, ← tor230_add, tor230_zero]
    linear_combination (norm := module) e
  rw [tor230_eq_iff] at e'
  clear * - e'
  omega

theorem lift_uv_comm_u_t131 (hU0 : U (𝔤 s 0) = (Type230.action h).φu (𝔤 s 0))
    (hU1 : U (𝔤 s 1) = (Type230.action h).φu (𝔤 s 1) + tor230 s u0 u1 u2)
    (hU2 : U (𝔤 s 2) = (Type230.action h).φu (𝔤 s 2) + tor230 s u3 u4 u5)
    (hV0 : V (𝔤 s 0) = (Type230.action h).φuv (𝔤 s 0))
    (hV1 : V (𝔤 s 1) = (Type230.action h).φuv (𝔤 s 1) + tor230 s v0 v1 v2)
    (hV2 : V (𝔤 s 2) = (Type230.action h).φuv (𝔤 s 2) + tor230 s v3 v4 v5)
    (hUV : U (V (𝔤 s 1)) = V (U (𝔤 s 1))) :
    2 ∣ v3 - v0 ∧ 2 ∣ v4 + u0 - v2 ∧ 2 ∣ v5 + u0 - v1 := by
  obtain ⟨p, Q, R, hAV⟩ := uv_gen1_par_t230 h
  obtain ⟨p', Q', R', hAU⟩ := u_gen1_par_t230 h
  have e := hUV
  rw [hV1, hU1, map_add U, map_add V, dev_tor230 U _ hU0 hU1 hU2, phiU_tor230 h,
    dev_tor230 V _ hV0 hV1 hV2, phiUV_tor230 h, hAV, dev_apply220 U _ hU0 hU1 hU2, ← hAV, hAU,
    dev_apply220 V _ hV0 hV1 hV2, ← hAU, SigmaFourAction.φu_φuv, odd_zsmul_tor230,
    even_zsmul_tor230, odd_zsmul_tor230, even_zsmul_tor230] at e
  simp only [add_zero] at e
  have e' : tor230 s (u0 + v0) (u1 + v2) (u2 + v1) =
      tor230 s (v3 + u0) (v4 + (u0 + u1)) (v5 + (u0 + u2)) := by
    rw [← tor230_add, ← tor230_add]
    linear_combination (norm := module) e
  rw [tor230_eq_iff] at e'
  clear * - e'
  omega

theorem lift_t_rho_t131 (hV0 : V (𝔤 s 0) = (Type230.action h).φuv (𝔤 s 0))
    (hV1 : V (𝔤 s 1) = (Type230.action h).φuv (𝔤 s 1) + tor230 s v0 v1 v2)
    (hV2 : V (𝔤 s 2) = (Type230.action h).φuv (𝔤 s 2) + tor230 s v3 v4 v5)
    (hVR : (Type230.action h).φρ (V ((Type230.action h).φρ ((Type230.action h).φρ (𝔤 s 1)))) =
      V ((Type230.action h).φρ ((Type230.action h).φρ (V ((Type230.action h).φρ (𝔤 s 1)))))) :
    2 ∣ v1 + v2 + v3 + v4 + 2 * v5 := by
  obtain ⟨p, Q, R, hA⟩ := uv_gen2_par_t230 h
  have hRt := phiR_tor230 h
  have eA := rho_uv_rel220 (Type230.action h).rels (𝔤 s 1)
  change (Type230.action h).φρ ((Type230.action h).φuv ((Type230.action h).φρ
    ((Type230.action h).φρ (𝔤 s 1)))) = (Type230.action h).φuv ((Type230.action h).φρ
    ((Type230.action h).φρ ((Type230.action h).φuv ((Type230.action h).φρ (𝔤 s 1))))) at eA
  have hRRA : (Type230.action h).φρ ((Type230.action h).φρ ((Type230.action h).φuv (𝔤 s 2))) =
      (p - 2 * Q) • 𝔤 s 0 + (2 * (R - Q) + 1) • 𝔤 s 1 + (2 * (-Q)) • 𝔤 s 2 := by
    rw [hA, phiR_apply_gens_t230 h, phiR_apply_gens_t230 h]
    module
  have e := hVR
  rw [phiR_gen1_t230 h, phiR_gen2_t230 h] at e eA
  have L : (Type230.action h).φρ (V ((-1 : ℤ) • 𝔤 s 0 + (-1 : ℤ) • 𝔤 s 1 + (-1 : ℤ) • 𝔤 s 2)) =
      (Type230.action h).φρ ((Type230.action h).φuv
        ((-1 : ℤ) • 𝔤 s 0 + (-1 : ℤ) • 𝔤 s 1 + (-1 : ℤ) • 𝔤 s 2)) +
      tor230 s (-1 * v0) (-1 * v2) (-1 * v1 + -1 * v2) +
      tor230 s (-1 * v3) (-1 * v5) (-1 * v4 + -1 * v5) := by
    rw [dev_apply220 V _ hV0 hV1 hV2, map_add (Type230.action h).φρ,
      map_add (Type230.action h).φρ, zsmul_tor230, zsmul_tor230, hRt, hRt]
  have Rh : V ((Type230.action h).φρ ((Type230.action h).φρ (V (𝔤 s 2)))) =
      (Type230.action h).φuv ((Type230.action h).φρ ((Type230.action h).φρ
        ((Type230.action h).φuv (𝔤 s 2)))) +
      tor230 s v0 v1 v2 + tor230 s v3 (v3 + (v4 + v5)) (v3 + (v5 + (v4 + v5))) := by
    rw [hV2, map_add (Type230.action h).φρ, map_add (Type230.action h).φρ, map_add V, hRRA,
      dev_apply220 V _ hV0 hV1 hV2, ← hRRA, odd_zsmul_tor230, even_zsmul_tor230, add_zero,
      hRt, hRt, dev_tor230 V _ hV0 hV1 hV2, phiUV_tor230 h]
  rw [L, Rh, eA] at e
  have e' : tor230 s (-1 * v0 + -1 * v3) (-1 * v2 + -1 * v5)
        ((-1 * v1 + -1 * v2) + (-1 * v4 + -1 * v5)) =
      tor230 s (v0 + v3) (v1 + (v3 + (v4 + v5))) (v2 + (v3 + (v5 + (v4 + v5)))) := by
    rw [← tor230_add, ← tor230_add]
    linear_combination (norm := module) e
  rw [tor230_eq_iff] at e'
  clear * - e'
  omega

end Relations

theorem lifts_t131 (h : Type230.Data s i F G)
    (V W U R : Torus (Type230.k s) →+ Torus (Type230.k s)) (hrels : SigmaFourRels V W U R)
    (hR0 : R (𝔤 s 0) = (Type230.action h).φρ (𝔤 s 0))
    (hR1 : R (𝔤 s 1) = (Type230.action h).φρ (𝔤 s 1))
    (hR2 : R (𝔤 s 2) = (Type230.action h).φρ (𝔤 s 2))
    (hU0 : U (𝔤 s 0) = (Type230.action h).φu (𝔤 s 0))
    (hU1 : (2 : ℤ) • U (𝔤 s 1) = (2 : ℤ) • (Type230.action h).φu (𝔤 s 1))
    (hU2 : (2 : ℤ) • U (𝔤 s 2) = (2 : ℤ) • (Type230.action h).φu (𝔤 s 2))
    (hV0 : V (𝔤 s 0) = (Type230.action h).φuv (𝔤 s 0))
    (hV1 : (2 : ℤ) • V (𝔤 s 1) = (2 : ℤ) • (Type230.action h).φuv (𝔤 s 1))
    (hV2 : (2 : ℤ) • V (𝔤 s 2) = (2 : ℤ) • (Type230.action h).φuv (𝔤 s 2)) :
    ∃ x q : ℤ, U (𝔤 s 1) = (Type230.action h).φu (𝔤 s 1) + tor230 s 0 0 x ∧
      U (𝔤 s 2) = (Type230.action h).φu (𝔤 s 2) + tor230 s 0 x 0 ∧
      V (𝔤 s 1) = (Type230.action h).φuv (𝔤 s 1) + tor230 s 0 0 q ∧
      V (𝔤 s 2) = (Type230.action h).φuv (𝔤 s 2) + tor230 s 0 q 0 := by
  have hR : R = (Type230.action h).φρ := torus_endo_ext_Idx4 _ _ fun j => by
    fin_cases j
    · exact hR0
    · exact hR1
    · exact hR2
  subst hR
  obtain ⟨u0, u1, u2, hu⟩ := exists_tor230 (s := s)
    (w := U (𝔤 s 1) - (Type230.action h).φu (𝔤 s 1)) (by rw [smul_sub, hU1, sub_self])
  obtain ⟨u3, u4, u5, hu'⟩ := exists_tor230 (s := s)
    (w := U (𝔤 s 2) - (Type230.action h).φu (𝔤 s 2)) (by rw [smul_sub, hU2, sub_self])
  obtain ⟨v0, v1, v2, hv⟩ := exists_tor230 (s := s)
    (w := V (𝔤 s 1) - (Type230.action h).φuv (𝔤 s 1)) (by rw [smul_sub, hV1, sub_self])
  obtain ⟨v3, v4, v5, hv'⟩ := exists_tor230 (s := s)
    (w := V (𝔤 s 2) - (Type230.action h).φuv (𝔤 s 2)) (by rw [smul_sub, hV2, sub_self])
  have hU1' : U (𝔤 s 1) = (Type230.action h).φu (𝔤 s 1) + tor230 s u0 u1 u2 := by
    rw [← hu]; abel
  have hU2' : U (𝔤 s 2) = (Type230.action h).φu (𝔤 s 2) + tor230 s u3 u4 u5 := by
    rw [← hu']; abel
  have hV1' : V (𝔤 s 1) = (Type230.action h).φuv (𝔤 s 1) + tor230 s v0 v1 v2 := by
    rw [← hv]; abel
  have hV2' : V (𝔤 s 2) = (Type230.action h).φuv (𝔤 s 2) + tor230 s v3 v4 v5 := by
    rw [← hv']; abel
  have k1 := lift_uv_sq_e_t131 h hV0 hV1' hV2' (DFunLike.congr_fun hrels.uv_sq (𝔤 s 1))
  have k2 := lift_uv_sq_f_t131 h hV0 hV1' hV2' (DFunLike.congr_fun hrels.uv_sq (𝔤 s 2))
  have k3 := lift_u_sq_t131 h hU0 hU1' hU2' (DFunLike.congr_fun hrels.u_sq (𝔤 s 1))
  have k4 := lift_u_rho_t131 h hU0 hU1' hU2' (DFunLike.congr_fun hrels.u_rho (𝔤 s 1))
  have k5 := lift_uv_comm_u_t131 h hU0 hU1' hU2' hV0 hV1' hV2'
    (DFunLike.congr_fun hrels.uv_comm_u (𝔤 s 1))
  have k6 := lift_t_rho_t131 h hV0 hV1' hV2' (rho_uv_rel220 hrels (𝔤 s 1))
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ : 2 ∣ 0 - u0 ∧ 2 ∣ 0 - u1 ∧
      2 ∣ u2 - u2 ∧ 2 ∣ 0 - u3 ∧ 2 ∣ u2 - u4 ∧ 2 ∣ 0 - u5 ∧ 2 ∣ 0 - v0 ∧ 2 ∣ 0 - v1 ∧
      2 ∣ v2 - v2 ∧ 2 ∣ 0 - v3 ∧ 2 ∣ v2 - v4 ∧ 2 ∣ 0 - v5 := by
    clear * - k1 k2 k3 k4 k5 k6
    omega
  refine ⟨u2, v2, ?_, ?_, ?_, ?_⟩
  · rw [hU1', tor230_congr d0 d1 d2]
  · rw [hU2', tor230_congr d3 d4 d5]
  · rw [hV1', tor230_congr d6 d7 d8]
  · rw [hV2', tor230_congr d9 d10 d11]

theorem tor230_eq_zero {x y z : ℤ} (hx : 2 ∣ x) (hy : 2 ∣ y) (hz : 2 ∣ z) :
    tor230 s x y z = 0 := by
  rw [← tor230_zero]
  exact tor230_congr (by simpa using hx.neg_right) (by simpa using hy.neg_right)
    (by simpa using hz.neg_right)

theorem t_eq_rho_uv220 {A : Type*} [AddCommGroup A] {V W U R : A →+ A}
    (hrels : SigmaFourRels V W U R) (y : A) : W y = R (V (R (R y))) := by
  have huvρ : ∀ y, R (V y) = W (R y) := fun y => DFunLike.congr_fun hrels.uv_rho y
  have hR3 : ∀ y, R (R (R y)) = y := fun y => DFunLike.congr_fun hrels.rho_cube y
  rw [huvρ, hR3]

theorem images_t131 (h : Type230.Data s i F G) (h' : Type231.Data s i F G)
    (V W U R : Torus (Type230.k s) →+ Torus (Type230.k s)) (hrels : SigmaFourRels V W U R)
    (hR0 : R (𝔤 s 0) = (Type230.action h).φρ (𝔤 s 0))
    (hR1 : R (𝔤 s 1) = (Type230.action h).φρ (𝔤 s 1))
    (hR2 : R (𝔤 s 2) = (Type230.action h).φρ (𝔤 s 2))
    (hU0 : U (𝔤 s 0) = (Type230.action h).φu (𝔤 s 0))
    (hU1 : (2 : ℤ) • U (𝔤 s 1) = (2 : ℤ) • (Type230.action h).φu (𝔤 s 1))
    (hU2 : (2 : ℤ) • U (𝔤 s 2) = (2 : ℤ) • (Type230.action h).φu (𝔤 s 2))
    (hV0 : V (𝔤 s 0) = (Type230.action h).φuv (𝔤 s 0))
    (hV1 : (2 : ℤ) • V (𝔤 s 1) = (2 : ℤ) • (Type230.action h).φuv (𝔤 s 1))
    (hV2 : (2 : ℤ) • V (𝔤 s 2) = (2 : ℤ) • (Type230.action h).φuv (𝔤 s 2))
    (hUe : U (𝔤 s 1) = (Type230.action h).φu (𝔤 s 1)) :
    (V = (Type230.action h).φuv ∧ W = (Type230.action h).φt ∧ U = (Type230.action h).φu ∧
      R = (Type230.action h).φρ) ∨
    (V = (act231 h').φuv ∧ W = (act231 h').φt ∧ U = (act231 h').φu ∧
      R = (act231 h').φρ) := by
  obtain ⟨x, q, hUx, hUx', hVq, hVq'⟩ :=
    lifts_t131 h V W U R hrels hR0 hR1 hR2 hU0 hU1 hU2 hV0 hV1 hV2
  have hR : R = (Type230.action h).φρ := torus_endo_ext_Idx4 _ _ fun j => by
    fin_cases j
    · exact hR0
    · exact hR1
    · exact hR2
  have hx : 2 ∣ 0 - x := by
    rw [hUe] at hUx
    have e : tor230 s 0 0 x = tor230 s 0 0 0 := by
      rw [tor230_zero]
      exact add_left_cancel (hUx.symm.trans (add_zero _).symm)
    exact (tor230_eq_iff.mp e).2.2
  have hU : U = (Type230.action h).φu := torus_endo_ext_Idx4 _ _ fun j => by
    fin_cases j
    · exact hU0
    · exact hUe
    · show U (𝔤 s 2) = (Type230.action h).φu (𝔤 s 2)
      rw [hUx', tor230_eq_zero (dvd_zero 2) (by simpa using hx) (dvd_zero 2), add_zero]
  have hW := t_eq_rho_uv220 hrels
  rcases Int.even_or_odd q with ⟨q', hq'⟩ | ⟨q', hq'⟩
  · left
    have hq : (2 : ℤ) ∣ q := ⟨q', by rw [hq']; ring⟩
    have hV : V = (Type230.action h).φuv := torus_endo_ext_Idx4 _ _ fun j => by
      fin_cases j
      · exact hV0
      · show V (𝔤 s 1) = (Type230.action h).φuv (𝔤 s 1)
        rw [hVq, tor230_eq_zero (dvd_zero 2) (dvd_zero 2) hq, add_zero]
      · show V (𝔤 s 2) = (Type230.action h).φuv (𝔤 s 2)
        rw [hVq', tor230_eq_zero (dvd_zero 2) hq (dvd_zero 2), add_zero]
    refine ⟨hV, AddMonoidHom.ext fun y => ?_, hU, hR⟩
    rw [hW, t_eq_rho_uv220 (Type230.action h).rels y, hR, hV]
  · right
    have hq : 2 ∣ 1 - q := ⟨-q', by rw [hq']; ring⟩
    have hV : V = (act231 h').φuv := torus_endo_ext_Idx4 _ _ fun j => by
      fin_cases j
      · exact hV0.trans (phiUV_gen0_t231_t230 h h').symm
      · show V (𝔤 s 1) = (act231 h').φuv (𝔤 s 1)
        rw [hVq, show tor230 s 0 0 q = tor230 s 0 0 1 from
          tor230_congr (by norm_num) (by norm_num) hq]
        exact (phiUV_gen1_t231_t230 h h').symm
      · show V (𝔤 s 2) = (act231 h').φuv (𝔤 s 2)
        rw [hVq', show tor230 s 0 q 0 = tor230 s 0 1 0 from
          tor230_congr (by norm_num) hq (by norm_num)]
        exact (phiUV_gen2_t231_t230 h h').symm
    have hU' : U = (act231 h').φu := AddMonoidHom.ext fun y => by
      rw [hU, phiU_t231_eq_t230 h h']
    have hR' : R = (act231 h').φρ := AddMonoidHom.ext fun y => by
      rw [hR, phiR_t231_eq_t230 h h']
    refine ⟨hV, AddMonoidHom.ext fun y => ?_, hU', hR'⟩
    rw [hW, t_eq_rho_uv220 (act231 h').rels y, hR', hV]

theorem rho_normalize_t230 (R : Torus (Type230.k s) →+ Torus (Type230.k s))
    (hR3 : ∀ x, R (R (R x)) = x) (hR0 : R (𝔤 s 0) = 𝔤 s 0) (hR1 : R (𝔤 s 1) = 𝔤 s 2)
    (hR2 : (2 : ℤ) • R (𝔤 s 2) =
      (2 : ℤ) • ((-1 : ℤ) • 𝔤 s 0 + (-1 : ℤ) • 𝔤 s 1 + (-1 : ℤ) • 𝔤 s 2)) :
    ∃ w : ℤ, (𝔤 s 1 + tor230 s w 0 0) + R (𝔤 s 1 + tor230 s w 0 0) +
      R (R (𝔤 s 1 + tor230 s w 0 0)) = -𝔤 s 0 := by
  obtain ⟨x, y, z, hτ⟩ := exists_tor230 (s := s)
    (w := R (𝔤 s 2) - ((-1 : ℤ) • 𝔤 s 0 + (-1 : ℤ) • 𝔤 s 1 + (-1 : ℤ) • 𝔤 s 2))
    (by rw [smul_sub, hR2, sub_self])
  have hR2' : R (𝔤 s 2) = (-1 : ℤ) • 𝔤 s 0 + (-1 : ℤ) • 𝔤 s 1 + (-1 : ℤ) • 𝔤 s 2 +
      tor230 s x y z := by
    rw [← hτ]; abel
  have hRt : ∀ a b c : ℤ, R (tor230 s a b c) = tor230 s (a - 4 * c) (-c) (b - c) := by
    intro a b c
    have e : tor230 s a b c = (a * 2 ^ (s + 1)) • 𝔤 s 0 + (b * 2 ^ (s + 3)) • 𝔤 s 1 +
        (c * 2 ^ (s + 3)) • 𝔤 s 2 := rfl
    have hc : (c * 2 ^ (s + 3)) • tor230 s x y z = 0 := by
      rw [show c * 2 ^ (s + 3) = 2 * (c * 2 ^ (s + 2)) by ring, even_zsmul_tor230]
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hR0, hR1, hR2', smul_add, hc,
      add_zero]
    simp only [tor230, pow_succ]
    module
  have hyz : 2 ∣ y ∧ 2 ∣ z := by
    have e := hR3 (𝔤 s 1)
    rw [hR1, hR2'] at e
    simp only [map_add, map_zsmul] at e
    rw [hR0, hR1, hR2', hRt] at e
    have e' : tor230 s (-1 * x + (x - 4 * z)) (-1 * y + -z) (-1 * z + (y - z)) =
        tor230 s 0 0 0 := by
      rw [tor230_zero, ← tor230_add, ← zsmul_tor230]
      linear_combination (norm := module) e
    rw [tor230_eq_iff] at e'
    clear * - e'
    omega
  have hx0 : R (tor230 s x 0 0) = tor230 s x 0 0 := by
    rw [hRt]
    congr 1 <;> ring
  have hz : tor230 s x y z = tor230 s x 0 0 := tor230_congr (by omega) (by omega) (by omega)
  refine ⟨x, ?_⟩
  simp only [map_add]
  rw [hR1, hR2', hz, hx0, hx0]
  have h4 : tor230 s x 0 0 + tor230 s x 0 0 + (tor230 s x 0 0 + tor230 s x 0 0) = 0 := by
    simp only [tor230_add]
    exact (tor230_congr ⟨-(2 * x), by ring⟩ (by norm_num) (by norm_num)).trans tor230_zero
  linear_combination (norm := module) h4

end Ext220

end CFSG.CGT.Stroth77
