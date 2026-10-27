module

import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Levi
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Link

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open Matrix CFSG.Fischer CFSG.ClassicalInvolution.WeakCT CFSG.EvenSmallLie.UnitarySix.YamadaEnd
open CFSG.ClassicalInvolution.Phan (blockIdx_val)
open scoped MatrixGroups

theorem det_scalar3 {r : F4} (hr : r ^ 3 = 1) : (scalar (Fin 3) r).det = 1 := by
  rw [scalar_apply, det_diagonal, Fin.prod_univ_three, ← pow_two, ← pow_succ, hr]

@[expose] def scal3 (r : F4) (hr : r ^ 3 = 1) : SL(3, F4) := ⟨scalar (Fin 3) r, det_scalar3 hr⟩

theorem scal3_mul {r s : F4} (hr : r ^ 3 = 1) (hs : s ^ 3 = 1) :
    scal3 r hr * scal3 s hs = scal3 (r * s) (by rw [mul_pow, hr, hs, one_mul]) := by
  apply Subtype.ext
  show scalar (Fin 3) r * scalar (Fin 3) s = scalar (Fin 3) (r * s)
  rw [map_mul]

theorem scal3_one : scal3 1 (one_pow 3) = 1 := Subtype.ext (by simp [scal3])

theorem tauSL_scal3 {r : F4} (hr : r ^ 3 = 1) : tauSL F4 (scal3 r hr) = scal3 r hr := by
  have hr2 : (r ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hr, one_pow]
  have hinv : (scal3 (r ^ 2) hr2)⁻¹ = scal3 r hr := by
    rw [inv_eq_iff_mul_eq_one, scal3_mul, ← scal3_one]
    apply Subtype.ext
    simp only [scal3, ← pow_succ, hr]
  have hfa : fieldAutSL (frobeniusEquiv F4 2) 3 (scal3 r hr) = scal3 (r ^ 2) hr2 := by
    apply Subtype.ext
    rw [coe_fieldAutSL]
    ext i j
    simp [scal3, scalar_apply, diagonal_apply, frobenius_def]
  apply Subtype.ext
  show antiDiagN F4 3 * (((fieldAutSL (frobeniusEquiv F4 2) 3 (scal3 r hr))⁻¹ :
    SL(3, F4)) : Matrix (Fin 3) (Fin 3) F4)ᵀ * antiDiagN F4 3 = scalar (Fin 3) r
  rw [hfa, hinv]
  simp only [scal3, scalar_apply, diagonal_transpose]
  rw [← scalar_apply, Matrix.mul_assoc, scalar_commute _ (fun _ => Commute.all _ _),
    ← Matrix.mul_assoc, antiDiagN_mul_self, Matrix.one_mul]

theorem cube_root (r : F4) (hr : r ^ 3 = 1) : r = 1 ∨ r = F4.ω ∨ r = F4.ω * F4.ω := by
  revert r
  decide

theorem theta1_scal3 {r : F4} (hr : r ^ 3 = 1) :
    ((theta1 F4 (scal3 r hr) : SL(6, F4)) : Matrix (Fin 6) (Fin 6) F4) = scalar (Fin 6) r := by
  rw [theta1_apply, tauSL_scal3]
  rcases cube_root r hr with rfl | rfl | rfl <;> decide +kernel +revert

theorem mem_center_SU0_of_scalar {g : SU0} {r : F4}
    (hg : ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = scalar (Fin 6) r) :
    g ∈ Subgroup.center SU0 := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hg]
  exact (scalar_commute r (fun _ => Commute.all _ _) _).symm


theorem psi0_scalar {B : SUJ} {r : F4}
    (hB : ((B : SpecialLinearGroup (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = scalar (Fin 6) r) :
    psi0 B = 1 := by
  have hc : conjQ B ∈ Subgroup.center SU0 := mem_center_SU0_of_scalar (r := r) (by
    rw [coe_conjQ, hB, Matrix.mul_assoc, scalar_commute r (fun _ => Commute.all _ _),
      ← Matrix.mul_assoc, Qm_mul_Qim, Matrix.one_mul])
  exact center_le_ker hc

@[expose] noncomputable def psiTheta : SL(3, F4) →* Equiv.Perm (Fin 693) := psi0.comp theta0

theorem center_le_ker_psiTheta : Subgroup.center SL(3, F4) ≤ psiTheta.ker := by
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hAe : A = scal3 r hr := Subtype.ext hrA.symm
  rw [MonoidHom.mem_ker, psiTheta, MonoidHom.comp_apply, hAe]
  exact psi0_scalar (r := r) (by rw [coe_theta0]; exact theta1_scal3 hr)

theorem card_SL3F4 : Nat.card SL(3, F4) = 60480 := by
  rw [Matrix.card_SL_field, F4.card]
  simp [Fin.prod_univ_three]

theorem card_SL2F4 : Nat.card SL(2, F4) = 60 := by
  rw [Matrix.card_SL_field, F4.card]
  simp [Fin.prod_univ_two]

theorem scal3_mem_center {r : F4} (hr : r ^ 3 = 1) : scal3 r hr ∈ Subgroup.center SL(3, F4) :=
  Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨r, by rw [Fintype.card_fin]; exact hr, rfl⟩

theorem three_le_card_center : 3 ≤ Nat.card (Subgroup.center SL(3, F4)) := by
  have h1 : (1 : F4) ^ 3 = 1 := by decide
  have h2 : F4.ω ^ 3 = 1 := by decide
  have h3 : (F4.ω * F4.ω) ^ 3 = 1 := by decide
  let f : Fin 3 → Subgroup.center SL(3, F4) := ![⟨_, scal3_mem_center h1⟩,
    ⟨_, scal3_mem_center h2⟩, ⟨_, scal3_mem_center h3⟩]
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg (fun x : Subgroup.center SL(3, F4) =>
      ((x : SL(3, F4)) : Matrix (Fin 3) (Fin 3) F4) 0 0) hab
    fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; revert this; decide +revert)
  have := Nat.card_le_card_of_injective f hf
  simpa using this


theorem psiTheta_eq {A : SL(3, F4)} {k : ℕ} (hk : k < 18) (h : yamGen k = theta0 A) :
    psiTheta A = wP [k] := by
  rw [psiTheta, MonoidHom.comp_apply, ← h, psi0_yamGen hk, wP_single]

theorem chK2_le_range : chK2.grp ≤ psiTheta.range := grp_le fun w hw => by
  simp only [chK2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, psiTheta_eq (by norm_num) yamGen0_eq⟩
  · exact ⟨_, psiTheta_eq (by norm_num) yamGen1_eq⟩
  · exact ⟨_, psiTheta_eq (by norm_num) yamGen2_eq⟩
  · exact ⟨_, psiTheta_eq (by norm_num) yamGen3_eq⟩
  · exact ⟨_, psiTheta_eq (by norm_num) yamGen15_eq⟩
  · exact ⟨_, psiTheta_eq (by norm_num) yamGen16_eq⟩

theorem range_psiTheta : psiTheta.range = chK2.grp := by
  refine (Subgroup.eq_of_le_of_card_ge chK2_le_range ?_).symm
  have h := Subgroup.card_ker_mul_card_range psiTheta
  rw [card_SL3F4] at h
  have hk : 3 ≤ Nat.card psiTheta.ker :=
    three_le_card_center.trans (Subgroup.card_le_of_le center_le_ker_psiTheta)
  rw [card_chK2]
  nlinarith

theorem ker_psiTheta : psiTheta.ker = Subgroup.center SL(3, F4) := by
  have h := Subgroup.card_ker_mul_card_range psiTheta
  rw [card_SL3F4, range_psiTheta, card_chK2] at h
  refine (Subgroup.eq_of_le_of_card_ge center_le_ker_psiTheta ?_).symm
  have : Nat.card psiTheta.ker = 3 := Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))
  rw [this]
  exact three_le_card_center

theorem transvection_congr' {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hik : i = k)
    (hjl : j = l) (c : F4) :
    SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection hkl c := by
  subst hik hjl
  rfl

theorem transvection_mem_B12 {a b : Fin 2} (hab : a ≠ b) {i j : Fin 3} (hij : i ≠ j)
    (hi : i.val = a.val) (hj : j.val = b.val) (c : F4) :
    SpecialLinearGroup.transvection hij c ∈ B12 F4 :=
  ⟨SpecialLinearGroup.transvection hab c, by
    rw [blockSL_transvection]
    exact transvection_congr' _ _ (Fin.ext (by simp [blockIdx_val, hi]))
      (Fin.ext (by simp [blockIdx_val, hj])) c⟩

theorem transvection_mem_B23 {a b : Fin 2} (hab : a ≠ b) {i j : Fin 3} (hij : i ≠ j)
    (hi : i.val = a.val + 1) (hj : j.val = b.val + 1) (c : F4) :
    SpecialLinearGroup.transvection hij c ∈ B23 F4 :=
  ⟨SpecialLinearGroup.transvection hab c, by
    rw [blockSL_transvection]
    exact transvection_congr' _ _ (Fin.ext (by simp [blockIdx_val, hi]; omega))
      (Fin.ext (by simp [blockIdx_val, hj]; omega)) c⟩

theorem card_map_le' {G H : Type*} [Group G] [Group H] (K : Subgroup G) (f : G →* H) [Finite K] :
    Nat.card (K.map f) ≤ Nat.card K :=
  Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective K)

theorem card_B12 : Nat.card (B12 F4) = 60 := by
  rw [B12, ← card_SL2F4]
  exact Nat.card_congr (MonoidHom.ofInjective (blockSL_injective (K := F4) (m := 3) (k := 2) (i := 0)
    (by omega))).toEquiv.symm

theorem card_B23 : Nat.card (B23 F4) = 60 := by
  rw [B23, ← card_SL2F4]
  exact Nat.card_congr (MonoidHom.ofInjective (blockSL_injective (K := F4) (m := 3) (k := 2) (i := 1)
    (by omega))).toEquiv.symm

theorem s1_mem_B12 : SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) (1 : F4) *
    SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1 *
    SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) 1 ∈ B12 F4 :=
  mul_mem (mul_mem (transvection_mem_B12 (a := 1) (b := 0) (by decide) _ rfl rfl 1)
    (transvection_mem_B12 (a := 0) (b := 1) (by decide) _ rfl rfl 1))
    (transvection_mem_B12 (a := 1) (b := 0) (by decide) _ rfl rfl 1)

theorem s2_mem_B23 : SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) (1 : F4) *
    SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) 1 *
    SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1 ∈ B23 F4 :=
  mul_mem (mul_mem (transvection_mem_B23 (a := 1) (b := 0) (by decide) _ rfl rfl 1)
    (transvection_mem_B23 (a := 0) (b := 1) (by decide) _ rfl rfl 1))
    (transvection_mem_B23 (a := 1) (b := 0) (by decide) _ rfl rfl 1)

theorem wP_conj (a b : ℕ) : wP [a, b, a] = wP [a] * wP [b] * wP [a] := by
  simp [wP, mul_assoc]

theorem map_B12 : (B12 F4).map psiTheta = chB12.grp := by
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · refine grp_le fun w hw => ?_
    simp only [chB12, List.mem_cons, List.not_mem_nil, or_false] at hw
    have h0 := psiTheta_eq (by norm_num) yamGen0_eq
    have h1 := psiTheta_eq (by norm_num) yamGen1_eq
    have h15 := psiTheta_eq (by norm_num) yamGen15_eq
    have hT0 := transvection_mem_B12 (a := 1) (b := 0) (by decide)
      (by decide : (1 : Fin 3) ≠ 0) rfl rfl (1 : F4)
    have hT1 := transvection_mem_B12 (a := 1) (b := 0) (by decide)
      (by decide : (1 : Fin 3) ≠ 0) rfl rfl F4.ω
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨_, hT0, h0⟩
    · exact ⟨_, hT1, h1⟩
    · refine ⟨_, mul_mem (mul_mem s1_mem_B12 hT0) s1_mem_B12, ?_⟩
      rw [map_mul, map_mul, h0, h15, wP_conj]
    · refine ⟨_, mul_mem (mul_mem s1_mem_B12 hT1) s1_mem_B12, ?_⟩
      rw [map_mul, map_mul, h1, h15, wP_conj]
  · rw [card_chB12, ← card_B12]
    exact card_map_le' _ _

theorem map_B23 : (B23 F4).map psiTheta = chB23.grp := by
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · refine grp_le fun w hw => ?_
    simp only [chB23, List.mem_cons, List.not_mem_nil, or_false] at hw
    have h2 := psiTheta_eq (by norm_num) yamGen2_eq
    have h3 := psiTheta_eq (by norm_num) yamGen3_eq
    have h16 := psiTheta_eq (by norm_num) yamGen16_eq
    have hT2 := transvection_mem_B23 (a := 1) (b := 0) (by decide)
      (by decide : (2 : Fin 3) ≠ 1) rfl rfl (1 : F4)
    have hT3 := transvection_mem_B23 (a := 1) (b := 0) (by decide)
      (by decide : (2 : Fin 3) ≠ 1) rfl rfl F4.ω
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨_, hT2, h2⟩
    · exact ⟨_, hT3, h3⟩
    · refine ⟨_, mul_mem (mul_mem s2_mem_B23 hT2) s2_mem_B23, ?_⟩
      rw [map_mul, map_mul, h2, h16, wP_conj]
    · refine ⟨_, mul_mem (mul_mem s2_mem_B23 hT3) s2_mem_B23, ?_⟩
      rw [map_mul, map_mul, h3, h16, wP_conj]
  · rw [card_chB23, ← card_B23]
    exact card_map_le' _ _

theorem card_map_B23 : Nat.card ((B23 F4).map psiTheta) = Nat.card (B23 F4) := by
  rw [map_B23, card_chB23, card_B23]

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
