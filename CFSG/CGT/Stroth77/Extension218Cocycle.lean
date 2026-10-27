module

public import CFSG.CGT.Stroth77.Extension218Bits
public import CFSG.CGT.Stroth77.Extension23

public section

namespace CFSG.CGT.Stroth77

open Matrix Ext218

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S}

theorem two_smul_ec_cocycle218 {τ : StrothTypeIndex} (D : StrothTypeData B τ)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hd2 : d * d = (D.c : S))
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    (φ : Torus τ.k →+ Torus τ.k) (hφ : ∀ x : B, D.ec (conjBy hgB x) = φ (D.ec x)) :
    (2 : ℤ) • D.ec b = φ (gen τ.k 0) - gen τ.k 0 := by
  rw [sq_rel_of_type D hBC hC hrel hdC hd2 hgC hgB hb
    (mul_inv_cancel_left D.c (conjBy hgB D.c)).symm, D.ec_mul, D.ec_inv, hφ, D.ec_c]
  abel

theorem conj_mul_adj218 (hBC : B ≤ C) {d : S} (hdC : d ∈ C) {z : B} (hz : z * z = 1)
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b) :
    conjBy hgC (⟨d * z, C.mul_mem hdC (hBC z.2)⟩ : C) =
      ⟨d * z, C.mul_mem hdC (hBC z.2)⟩ * Subgroup.inclusion hBC (z * b * conjBy hgB z) := by
  have hdC' : (⟨d * z, C.mul_mem hdC (hBC z.2)⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC z := Subtype.ext rfl
  have hz' : Subgroup.inclusion hBC z * Subgroup.inclusion hBC z = 1 := by
    rw [← map_mul, hz, map_one]
  rw [hdC', conjBy_mul, hb, conjBy_inclusion hBC hgC hgB, map_mul, map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (Subgroup.inclusion hBC z) (Subgroup.inclusion hBC z), hz', one_mul]

section T221

variable {s : ℕ} {hs : 1 ≤ s}

theorem m_t221 : (StrothTypeIndex.t221 s hs).m = s + 2 := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t221 s hs)) 0
  simp only [Matrix.cons_val_zero] at h
  exact h.symm

theorem n_t221 : (StrothTypeIndex.t221 s hs).n = s + 4 := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t221 s hs)) 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
  exact h.symm

theorem ec_conj_u_t221 (D : StrothTypeData B (StrothTypeIndex.t221 s hs)) (x : B) :
    D.ec (conjBy D.u_mem x) = (Type221.action (Type221.data s)).φu (D.ec x) :=
  D.u_conj x

theorem ec_conj_ρ_t221 (D : StrothTypeData B (StrothTypeIndex.t221 s hs)) (x : B) :
    D.ec (conjBy D.ρ_mem x) = (Type221.action (Type221.data s)).φρ (D.ec x) :=
  D.ρ_conj x

theorem ec_conj_t_t221 (D : StrothTypeData B (StrothTypeIndex.t221 s hs)) (x : B) :
    D.ec (conjBy D.t_mem x) = (Type221.action (Type221.data s)).φt (D.ec x) :=
  D.t_conj x

theorem ec_conj_uv_t221 (D : StrothTypeData B (StrothTypeIndex.t221 s hs)) (x : B) :
    D.ec (conjBy D.uv_mem x) = (Type221.action (Type221.data s)).φuv (D.ec x) :=
  D.uv_conj x

theorem ec_a_t221 (D : StrothTypeData B (StrothTypeIndex.t221 s hs)) :
    D.ec D.a = gen (Type221.k s) 1 :=
  D.ec_a

theorem ec_b_t221 (D : StrothTypeData B (StrothTypeIndex.t221 s hs)) :
    D.ec D.b = gen (Type221.k s) 2 :=
  D.ec_b

theorem exists_bits_of_two_smul_eq_t221 {ω b : Torus (Type221.k s)}
    (h : (2 : ℤ) • ω = (2 : ℤ) • b) :
    ∃ x y z : ℕ, x ≤ 1 ∧ ω = b + bv221 s x y z := by
  have h0 : (2 : ℤ) • (ω - b) = 0 := by rw [smul_sub, h, sub_self]
  obtain ⟨x, y, z, hx, -, -, hω⟩ := exists_bits_of_two_smul_eq_zero
    (by change 1 ≤ s + 2; omega) (by change 1 ≤ s + 4; omega) (by change 1 ≤ s + 4; omega) h0
  refine ⟨x, y, z, hx, ?_⟩
  rw [bv221, ← hω]
  abel

theorem exists_normal_form_t221 (D : StrothTypeData B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S)) :
    ∃ (d' : S) (hd'C : d' ∈ C), d' ∉ B ∧ d' * d' = (D.c : S) ∧ ∃ ε : ℕ, ε ≤ 1 ∧
      (∃ b : B, conjBy (hL D.u_mem_L) (⟨d', hd'C⟩ : C) =
          ⟨d', hd'C⟩ * Subgroup.inclusion hBC b ∧ D.ec b = baseU221 s + bv221 s ε 0 0) ∧
      (∃ b : B, conjBy (hL D.ρ_mem_L) (⟨d', hd'C⟩ : C) =
          ⟨d', hd'C⟩ * Subgroup.inclusion hBC b ∧ D.ec b = 0) ∧
      (∃ b : B, conjBy (hL D.t_mem_L) (⟨d', hd'C⟩ : C) =
          ⟨d', hd'C⟩ * Subgroup.inclusion hBC b ∧
            D.ec b = baseT221 s (Type120.GV (s + 4)) + bv221 s 0 0 ε) ∧
      (∃ b : B, conjBy (hL D.uv_mem_L) (⟨d', hd'C⟩ : C) =
          ⟨d', hd'C⟩ * Subgroup.inclusion hBC b ∧
            D.ec b = baseUV221 s (Type120.GV (s + 4)) + bv221 s 0 ε 0) := by
  classical
  obtain ⟨βu, hβu⟩ := exists_conj_eq hBC hrel hdC hdB D.u (hL D.u_mem_L) D.u_mem
  obtain ⟨βr, hβr⟩ := exists_conj_eq hBC hrel hdC hdB D.ρ (hL D.ρ_mem_L) D.ρ_mem
  obtain ⟨βt, hβt⟩ := exists_conj_eq hBC hrel hdC hdB D.t (hL D.t_mem_L) D.t_mem
  obtain ⟨βv, hβv⟩ := exists_conj_eq hBC hrel hdC hdB D.uv (hL D.uv_mem_L) D.uv_mem
  have sU : (2 : ℤ) • D.ec βu = (Type221.action (Type221.data s)).φu (gen (Type221.k s) 0) -
      gen (Type221.k s) 0 :=
    two_smul_ec_cocycle218 D hBC hC hrel hdC hd2 (hL D.u_mem_L) D.u_mem hβu _ (ec_conj_u_t221 D)
  have sR : (2 : ℤ) • D.ec βr = (Type221.action (Type221.data s)).φρ (gen (Type221.k s) 0) -
      gen (Type221.k s) 0 :=
    two_smul_ec_cocycle218 D hBC hC hrel hdC hd2 (hL D.ρ_mem_L) D.ρ_mem hβr _ (ec_conj_ρ_t221 D)
  have sT : (2 : ℤ) • D.ec βt = (Type221.action (Type221.data s)).φt (gen (Type221.k s) 0) -
      gen (Type221.k s) 0 :=
    two_smul_ec_cocycle218 D hBC hC hrel hdC hd2 (hL D.t_mem_L) D.t_mem hβt _ (ec_conj_t_t221 D)
  have sV : (2 : ℤ) • D.ec βv = (Type221.action (Type221.data s)).φuv (gen (Type221.k s) 0) -
      gen (Type221.k s) 0 :=
    two_smul_ec_cocycle218 D hBC hC hrel hdC hd2 (hL D.uv_mem_L) D.uv_mem hβv _
      (ec_conj_uv_t221 D)
  obtain ⟨xu, yu, zu, hxu, hU⟩ :=
    exists_bits_of_two_smul_eq_t221 (sU.trans (phiU_gen0_sub_t221 (Type221.data s)))
  obtain ⟨xr, yr, zr, -, hR⟩ :=
    exists_bits_of_two_smul_eq_t221 (sR.trans (phiR_gen0_sub_t221 (Type221.data s)))
  obtain ⟨xt, yt, zt, -, hT⟩ :=
    exists_bits_of_two_smul_eq_t221 (sT.trans (phiT_gen0_sub_t221 (Type221.data s)))
  obtain ⟨xv, yv, zv, -, hV⟩ :=
    exists_bits_of_two_smul_eq_t221 (sV.trans (phiUV_gen0_sub_t221 (Type221.data s)))
  rw [zero_add] at hR
  have E1 := inv_rel_of_type D hBC hdC (hL D.u_mem_L) D.u_mem hβu D.u_sq _ (ec_conj_u_t221 D)
  have E2 := inv_rel_three_of_type D hBC hdC (hL D.ρ_mem_L) D.ρ_mem hβr D.rho_cube _
    (ec_conj_ρ_t221 D)
  have E3 := inv_rel_of_type D hBC hdC (hL D.uv_mem_L) D.uv_mem hβv D.uv_sq _
    (ec_conj_uv_t221 D)
  have E4 := inv_rel_of_type D hBC hdC (hL D.t_mem_L) D.t_mem hβt D.t_sq _ (ec_conj_t_t221 D)
  have E5 := rel_u_rho_of_type D hBC hdC (hL D.u_mem_L) (hL D.ρ_mem_L) hβu hβr _ _
    (ec_conj_u_t221 D) (ec_conj_ρ_t221 D)
  have E6 := rel_uv_comm_u_of_type D hBC hdC (hL D.u_mem_L) (hL D.uv_mem_L) hβu hβv _ _
    (ec_conj_u_t221 D) (ec_conj_uv_t221 D)
  have E7 := rel_t_rho_of_type D hBC hdC (hL D.t_mem_L) (hL D.ρ_mem_L) (hL D.uv_mem_L) hβt hβr
    hβv _ _ _ (ec_conj_t_t221 D) (ec_conj_ρ_t221 D) (ec_conj_uv_t221 D)
  rw [hU] at E1
  rw [hR] at E2
  rw [hV] at E3
  rw [hT] at E4
  rw [hU, hR] at E5
  rw [hU, hV] at E6
  rw [hR, hT, hV] at E7
  obtain ⟨A1, A2, A3, A4⟩ := adjust_bits_t221 (Type221.data s)
    (bits_of_relations_t221 (Type221.data s) E1 E2 E3 E4 E5 E6 E7)
  set z : B := Additive.toMul (D.e.symm (bv221 s zv zr (yr + zr))) with hzdef
  have hzec : D.ec z = bv221 s zv zr (yr + zr) := by
    rw [hzdef]
    exact D.e.apply_symm_apply _
  have hz2 : z * z = 1 := by
    apply D.ec_eq_zero_iff.mp
    rw [D.ec_mul, hzec]
    exact (two_zsmul _).symm.trans (two_smul_bv221 _ _ _)
  have hz2S : (z : S) * z = 1 := by
    rw [← Subgroup.coe_mul, hz2, Subgroup.coe_one]
  have hcomm : (z : S) * d = d * z :=
    Subgroup.mem_centralizer_iff.mp (hC hdC) (z : S) z.2
  refine ⟨d * z, C.mul_mem hdC (hBC z.2), ?_, ?_, xu, hxu, ?_, ?_, ?_, ?_⟩
  · intro hmem
    apply hdB
    have hd : d = d * z * z := by rw [mul_assoc, hz2S, mul_one]
    rw [hd]
    exact B.mul_mem hmem z.2
  · calc d * z * (d * z) = d * (z * d) * z := by group
      _ = d * (d * z) * z := by rw [hcomm]
      _ = d * d * (z * z) := by group
      _ = D.c := by rw [hz2S, mul_one, hd2]
  · refine ⟨z * βu * conjBy D.u_mem z,
      conj_mul_adj218 hBC hdC hz2 (hL D.u_mem_L) D.u_mem hβu, ?_⟩
    have key : bv221 s zv zr (yr + zr) + (baseU221 s + bv221 s xu yu zu) +
        (Type221.action (Type221.data s)).φu (bv221 s zv zr (yr + zr)) =
        baseU221 s + bv221 s xu 0 0 := by
      rw [← A1]
      abel
    rw [D.ec_mul, D.ec_mul, ec_conj_u_t221 D, hzec, hU]
    exact key
  · refine ⟨z * βr * conjBy D.ρ_mem z,
      conj_mul_adj218 hBC hdC hz2 (hL D.ρ_mem_L) D.ρ_mem hβr, ?_⟩
    rw [D.ec_mul, D.ec_mul, ec_conj_ρ_t221 D, hzec, hR]
    exact A2.trans bv221_zero
  · refine ⟨z * βt * conjBy D.t_mem z,
      conj_mul_adj218 hBC hdC hz2 (hL D.t_mem_L) D.t_mem hβt, ?_⟩
    have key : bv221 s zv zr (yr + zr) + (baseT221 s (Type120.GV (s + 4)) + bv221 s xt yt zt) +
        (Type221.action (Type221.data s)).φt (bv221 s zv zr (yr + zr)) =
        baseT221 s (Type120.GV (s + 4)) + bv221 s 0 0 xu := by
      rw [← A3]
      abel
    rw [D.ec_mul, D.ec_mul, ec_conj_t_t221 D, hzec, hT]
    exact key
  · refine ⟨z * βv * conjBy D.uv_mem z,
      conj_mul_adj218 hBC hdC hz2 (hL D.uv_mem_L) D.uv_mem hβv, ?_⟩
    have key : bv221 s zv zr (yr + zr) +
        (baseUV221 s (Type120.GV (s + 4)) + bv221 s xv yv zv) +
        (Type221.action (Type221.data s)).φuv (bv221 s zv zr (yr + zr)) =
        baseUV221 s (Type120.GV (s + 4)) + bv221 s 0 xu 0 := by
      rw [← A4]
      abel
    rw [D.ec_mul, D.ec_mul, ec_conj_uv_t221 D, hzec, hV]
    exact key

end T221

end CFSG.CGT.Stroth77
