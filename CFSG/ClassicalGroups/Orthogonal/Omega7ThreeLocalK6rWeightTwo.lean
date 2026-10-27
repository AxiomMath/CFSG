module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRootOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K]

@[expose] def SuppPlaneTwoZ (w : Idx → K) : Prop :=
  w (.inl 0) = 0 ∧ w (.inr (.inl 0)) = 0 ∧ w (.inl 1) = 0 ∧ w (.inr (.inl 1)) = 0

@[expose] def SuppPlanesZeroOne (w : Idx → K) : Prop :=
  w (.inl 2) = 0 ∧ w (.inr (.inl 2)) = 0 ∧ w (.inr (.inr ())) = 0

theorem modelPolar_eq_zero_of_supp (a : K) {u w : Idx → K} (hu : SuppPlaneTwoZ u)
    (hw : SuppPlanesZeroOne w) : modelPolar K a u w = 0 := by
  obtain ⟨hu0, hu0', hu1, hu1'⟩ := hu
  obtain ⟨hw2, hw2', hwz⟩ := hw
  simp [modelPolar, Fin.sum_univ_three, hu0, hu0', hu1, hu1', hw2, hw2', hwz]

theorem rotMat_mulVec_eq_self_of_suppPlaneTwoZ {v : Fin 3 → ZMod 3} (hv : v 2 = 0)
    {w : Idx → K} (hw : SuppPlaneTwoZ w) : rotMat K v *ᵥ w = w := by
  obtain ⟨h0, h0', h1, h1'⟩ := hw
  funext a
  rcases a with i | i | u
  · rw [rotMat_mulVec_inl]
    fin_cases i <;> simp [h0, h0', h1, h1', hv, planeRot_zero]
  · rw [rotMat_mulVec_inr_inl]
    fin_cases i <;> simp [h0, h0', h1, h1', hv, planeRot_zero]
  · rw [rotMat_mulVec_inr_inr]

private def siegelT (l₁ l₂ : K) : Idx → K := vecOf K ![1, l₁, 0] ![0, l₂, 0] 0

private def siegelT' (l₁ l₂ : K) : Idx → K := vecOf K ![0, -l₂, 0] ![1, l₁ - l₂, 0] 0

private def siegelT'' (l₁ l₂ : K) : Idx → K := vecOf K ![-1, l₂ - l₁, 0] ![-1, -l₁, 0] 0

private theorem siegelT_quad (a l₁ l₂ : K) (hl : l₁ ^ 2 - l₁ * l₂ + l₂ ^ 2 = -1) :
    modelQuad K a (siegelT l₁ l₂) = 0 := by
  rw [siegelT, modelQuad_vecOf]
  simp
  linear_combination hl

private theorem siegelT'_quad (a l₁ l₂ : K) (hl : l₁ ^ 2 - l₁ * l₂ + l₂ ^ 2 = -1) :
    modelQuad K a (siegelT' l₁ l₂) = 0 := by
  rw [siegelT', modelQuad_vecOf]
  simp
  linear_combination hl

private theorem siegelT''_quad (a l₁ l₂ : K) (hl : l₁ ^ 2 - l₁ * l₂ + l₂ ^ 2 = -1) :
    modelQuad K a (siegelT'' l₁ l₂) = 0 := by
  rw [siegelT'', modelQuad_vecOf]
  simp
  linear_combination hl

private theorem siegelT_polar_T' (a l₁ l₂ : K) (hl : l₁ ^ 2 - l₁ * l₂ + l₂ ^ 2 = -1) :
    modelPolar K a (siegelT l₁ l₂) (siegelT' l₁ l₂) = 0 := by
  rw [siegelT, siegelT', modelPolar_vecOf]
  simp
  linear_combination (-1 : K) * hl

private theorem siegelT'_polar_T'' (a l₁ l₂ : K) (hl : l₁ ^ 2 - l₁ * l₂ + l₂ ^ 2 = -1) :
    modelPolar K a (siegelT' l₁ l₂) (siegelT'' l₁ l₂) = 0 := by
  rw [siegelT', siegelT'', modelPolar_vecOf]
  simp
  linear_combination (-1 : K) * hl

private theorem siegelT_add (l₁ l₂ : K) :
    siegelT l₁ l₂ + siegelT' l₁ l₂ + siegelT'' l₁ l₂ = 0 := by
  funext a
  rcases a with i | i | u
  · fin_cases i <;> simp [siegelT, siegelT', siegelT''] <;> ring
  · fin_cases i <;> simp [siegelT, siegelT', siegelT''] <;> ring
  · simp [siegelT, siegelT', siegelT'', vecOf]

private theorem siegelT_modelPolar_x0 (a l₁ l₂ : K) :
    modelPolar K a (vecOf K ![1, 0, 0] 0 0)
      (vecOf K ![1, l₁, 0] ![0, l₂, 0] 0) = 2 := by
  rw [modelPolar_vecOf]
  simp

private theorem siegelT'_modelPolar_x0 (a l₁ l₂ : K) :
    modelPolar K a (vecOf K ![1, 0, 0] 0 0)
      (vecOf K ![0, -l₂, 0] ![1, l₁ - l₂, 0] 0) = -1 := by
  rw [modelPolar_vecOf]
  simp

private theorem siegel_rot_zero_T (l₁ l₂ : K) {v : Fin 3 → ZMod 3} (h0 : v 0 = 0)
    (h1 : v 1 = 0) : rotMat K v *ᵥ siegelT l₁ l₂ = siegelT l₁ l₂ := by
  rw [siegelT, rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, rfl⟩ <;> fin_cases i <;>
    simp [planeRot_zero, h0, h1] <;> ring

private theorem siegel_rot_zero_T' (l₁ l₂ : K) {v : Fin 3 → ZMod 3} (h0 : v 0 = 0)
    (h1 : v 1 = 0) : rotMat K v *ᵥ siegelT' l₁ l₂ = siegelT' l₁ l₂ := by
  rw [siegelT', rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, rfl⟩ <;> fin_cases i <;>
    simp [planeRot_zero, h0, h1] <;> ring

private theorem siegel_rot_one_T (l₁ l₂ : K) {v : Fin 3 → ZMod 3} (h0 : v 0 = 1)
    (h1 : v 1 = 1) : rotMat K v *ᵥ siegelT l₁ l₂ = siegelT' l₁ l₂ := by
  rw [siegelT, siegelT', rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, rfl⟩ <;> fin_cases i <;>
    simp [planeRot_one, h0, h1] <;> ring

private theorem siegel_rot_one_T' (l₁ l₂ : K) {v : Fin 3 → ZMod 3} (h0 : v 0 = 1)
    (h1 : v 1 = 1) : rotMat K v *ᵥ siegelT' l₁ l₂ = siegelT'' l₁ l₂ := by
  rw [siegelT', siegelT'', rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, rfl⟩ <;> fin_cases i <;>
    simp [planeRot_one, h0, h1] <;> ring

private theorem siegel_rot_two_T (l₁ l₂ : K) {v : Fin 3 → ZMod 3} (h0 : v 0 = 2)
    (h1 : v 1 = 2) : rotMat K v *ᵥ siegelT l₁ l₂ = siegelT'' l₁ l₂ := by
  rw [siegelT, siegelT'', rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, rfl⟩ <;> fin_cases i <;>
    simp [planeRot_two, h0, h1] <;> ring

private theorem siegel_rot_two_T' (l₁ l₂ : K) {v : Fin 3 → ZMod 3} (h0 : v 0 = 2)
    (h1 : v 1 = 2) : rotMat K v *ᵥ siegelT' l₁ l₂ = siegelT l₁ l₂ := by
  rw [siegelT', siegelT, rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, rfl⟩ <;> fin_cases i <;>
    simp [planeRot_two, h0, h1] <;> ring

theorem exists_siegel_pair_planes_zero_one [Finite K] (F : Frame K) :
    ∃ t t' : Idx → K, modelQuad K F.a t = 0 ∧ modelPolar K F.a t t' = 0 ∧
      SuppPlanesZeroOne t ∧ SuppPlanesZeroOne t' ∧
      (∀ v : F3Cube, Multiplicative.toAdd v 0 = Multiplicative.toAdd v 1 →
        Commute (c₀ F v) (omegaRoot F t t')) ∧
      ((F.P⁻¹ * omegaRootGL F t t' * F.P : GL Idx K) : Matrix Idx Idx K) *ᵥ
        vecOf K ![1, 0, 0] 0 0 ≠ vecOf K ![1, 0, 0] 0 0 := by
  obtain ⟨l₁, l₂, hl⟩ := exists_planeNorm_eq F.hK F.h3 (-1)
  refine ⟨siegelT l₁ l₂, siegelT' l₁ l₂, siegelT_quad F.a l₁ l₂ hl,
    siegelT_polar_T' F.a l₁ l₂ hl, ?_, ?_, ?_, ?_⟩
  · simp [SuppPlanesZeroOne, siegelT]
  · simp [SuppPlanesZeroOne, siegelT']
  · intro v hv
    have hconj := omegaRoot_conj_c₀ F v (siegelT l₁ l₂) (siegelT' l₁ l₂)
    have hcyc1 : omegaRoot F (siegelT' l₁ l₂) (siegelT'' l₁ l₂) =
        omegaRoot F (siegelT l₁ l₂) (siegelT' l₁ l₂) :=
      omegaRoot_cyclic F (siegelT_add l₁ l₂) (siegelT_quad F.a l₁ l₂ hl)
        (siegelT'_quad F.a l₁ l₂ hl) (siegelT_polar_T' F.a l₁ l₂ hl)
    rcases zmod3_cases (Multiplicative.toAdd v 0) with hk | hk | hk
    · have h1 : Multiplicative.toAdd v 1 = 0 := hv ▸ hk
      rw [siegel_rot_zero_T l₁ l₂ hk h1, siegel_rot_zero_T' l₁ l₂ hk h1] at hconj
      exact mul_inv_eq_iff_eq_mul.mp hconj
    · have h1 : Multiplicative.toAdd v 1 = 1 := hv ▸ hk
      rw [siegel_rot_one_T l₁ l₂ hk h1, siegel_rot_one_T' l₁ l₂ hk h1] at hconj
      exact mul_inv_eq_iff_eq_mul.mp (hconj.trans hcyc1)
    · have h1 : Multiplicative.toAdd v 1 = 2 := hv ▸ hk
      rw [siegel_rot_two_T l₁ l₂ hk h1, siegel_rot_two_T' l₁ l₂ hk h1] at hconj
      have hcyc2 : omegaRoot F (siegelT'' l₁ l₂) (siegelT l₁ l₂) =
          omegaRoot F (siegelT' l₁ l₂) (siegelT'' l₁ l₂) := by
        refine omegaRoot_cyclic F ?_ (siegelT'_quad F.a l₁ l₂ hl)
          (siegelT''_quad F.a l₁ l₂ hl) (siegelT'_polar_T'' F.a l₁ l₂ hl)
        simpa [add_comm, add_left_comm, add_assoc] using siegelT_add l₁ l₂
      exact mul_inv_eq_iff_eq_mul.mp (hconj.trans (hcyc2.trans hcyc1))
  · rw [omegaRootGL_model_apply F (siegelT_quad F.a l₁ l₂ hl)
      (siegelT_polar_T' F.a l₁ l₂ hl)]
    intro h
    have hB := siegelT_modelPolar_x0 F.a l₁ l₂
    have hB' := siegelT'_modelPolar_x0 F.a l₁ l₂
    have hQ' : modelQuad K F.a (vecOf K ![0, -l₂, 0] ![1, l₁ - l₂, 0] 0) = 0 := by
      simpa [siegelT'] using siegelT'_quad F.a l₁ l₂ hl
    have hc := congrFun h (.inl 0)
    simp [hB, hB', hQ', siegelT, siegelT'] at hc

theorem exists_root_pair_plane_two [Finite K] (F : Frame K) :
    ∃ u w : Idx → K, modelQuad K F.a u = 0 ∧ modelPolar K F.a u w = 0 ∧
      SuppPlaneTwoZ u ∧ SuppPlaneTwoZ w ∧ omegaRoot F u w ≠ 1 := by
  obtain ⟨p₁, p₂, hp⟩ := exists_planeNorm_eq F.hK F.h3 (-F.a)
  refine ⟨vecOf K ![0, 0, p₁] ![0, 0, p₂] 1,
    vecOf K ![0, 0, p₁ - 2 * p₂] ![0, 0, 2 * p₁ - p₂] 0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [modelQuad_vecOf]
    simp
    linear_combination hp
  · rw [modelPolar_vecOf]
    simp
    ring
  · simp [SuppPlaneTwoZ]
  · simp [SuppPlaneTwoZ]
  · refine omegaRoot_ne_one_of_not_mem_span F ?_ ?_ ?_ ?_
    · rw [modelQuad_vecOf]
      simp
      linear_combination hp
    · intro h
      have := congrFun h (.inr (.inr ()))
      simp at this
    · rw [modelPolar_vecOf]
      simp
      ring
    · intro c hc
      have hz : c = 0 := by
        simpa using (congrFun hc (.inr (.inr ()))).symm
      rw [hz] at hc
      have h1 := congrFun hc (.inl 2)
      have h2 := congrFun hc (.inr (.inl 2))
      simp at h1 h2
      have hp₂ : p₂ = 0 := by
        have h3 : 3 * p₂ = 0 := by linear_combination h2 - 2 * h1
        exact (mul_eq_zero.mp h3).resolve_left F.h3
      have hp₁ : p₁ = 0 := by simpa [hp₂] using h1
      have hha : (0 : K) = -F.a := by simpa [hp₁, hp₂] using hp
      exact F.a_ne_zero (neg_eq_zero.mp hha.symm)

theorem exists_commuting_pair_weight_two [Finite K] (F : Frame K) :
    ∃ x y : ↥(Omega7 K),
      (∀ v : F3Cube, Multiplicative.toAdd v 2 = 0 → Commute (c₀ F v) x) ∧
      (∀ v : F3Cube, Multiplicative.toAdd v 0 = Multiplicative.toAdd v 1 → Commute (c₀ F v) y) ∧
      orderOf x = ringChar K ∧ orderOf y = ringChar K ∧ Commute x y ∧
      y ∉ Subgroup.zpowers x := by
  obtain ⟨u, w, hQu, hBuw, hsuppu, hsuppw, hxne⟩ := exists_root_pair_plane_two F
  obtain ⟨t, t', hQt, hBtt', hsuppt, hsuppt', hcomm, hmove⟩ :=
    exists_siegel_pair_planes_zero_one F
  have hx0supp : SuppPlanesZeroOne (vecOf K ![1, 0, 0] 0 0) := by
    simp [SuppPlanesZeroOne]
  have hBx0u : modelPolar K F.a (vecOf K ![1, 0, 0] 0 0) u = 0 := by
    rw [modelPolar_comm]
    exact modelPolar_eq_zero_of_supp F.a hsuppu hx0supp
  have hBx0w : modelPolar K F.a (vecOf K ![1, 0, 0] 0 0) w = 0 := by
    rw [modelPolar_comm]
    exact modelPolar_eq_zero_of_supp F.a hsuppw hx0supp
  refine ⟨omegaRoot F u w, omegaRoot F t t', ?_, hcomm, orderOf_omegaRoot F hxne, ?_, ?_, ?_⟩
  · intro v hv
    exact commute_c₀_omegaRoot F v
      (rotMat_mulVec_eq_self_of_suppPlaneTwoZ (v := Multiplicative.toAdd v) hv hsuppu)
      (rotMat_mulVec_eq_self_of_suppPlaneTwoZ (v := Multiplicative.toAdd v) hv hsuppw)
  · apply orderOf_omegaRoot F
    intro h1
    apply hmove
    have h1' : omegaRootGL F t t' = 1 := by
      have := congrArg Subtype.val h1
      simpa [coe_omegaRoot] using this
    rw [h1']
    simp
  · exact commute_omegaRoot_of_polar_eq_zero F
      (modelPolar_eq_zero_of_supp F.a hsuppu hsuppt)
      (modelPolar_eq_zero_of_supp F.a hsuppu hsuppt')
      (modelPolar_eq_zero_of_supp F.a hsuppw hsuppt)
      (modelPolar_eq_zero_of_supp F.a hsuppw hsuppt')
  · rintro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hBkw : modelPolar K F.a u (k • w) = 0 := by
      rw [← Int.cast_smul_eq_zsmul K, modelPolar_smul_right, hBuw, mul_zero]
    have hk' : omegaRootGL F u (k • w) = omegaRootGL F t t' := by
      have h1 : omegaRoot F u w ^ k = omegaRoot F t t' := hk
      rw [omegaRoot_zpow F hBuw] at h1
      exact congrArg Subtype.val h1
    have hBx0kw : modelPolar K F.a (vecOf K ![1, 0, 0] 0 0) (k • w) = 0 := by
      rw [← Int.cast_smul_eq_zsmul K, modelPolar_smul_right, hBx0w, mul_zero]
    apply hmove
    rw [← hk', omegaRootGL_model_apply F hQu hBkw, hBx0u, hBx0kw]
    simp

theorem two_le_pRank_centralizer_c₀_weight_two [Finite K] (F : Frame K) :
    2 ≤ pRank (ringChar K)
      (Subgroup.centralizer ({c₀ F (Multiplicative.ofAdd ![1, 1, 0])} : Set ↥(Omega7 K))) := by
  obtain ⟨x, y, hx, hy, hxo, hyo, hxy, hyx⟩ := exists_commuting_pair_weight_two F
  exact two_le_pRank_ringChar_of_commute
    (Subgroup.mem_centralizer_singleton_iff.mpr (hx _ rfl).symm)
    (Subgroup.mem_centralizer_singleton_iff.mpr (hy _ rfl).symm) hxo hyo hxy hyx

theorem one_le_pRank_centralizer_c₀_pair_e₀_e₁ [Finite K] (F : Frame K) :
    1 ≤ pRank (ringChar K)
      (Subgroup.centralizer ({c₀ F (Multiplicative.ofAdd ![1, 0, 0]),
        c₀ F (Multiplicative.ofAdd ![0, 1, 0])} : Set ↥(Omega7 K))) := by
  obtain ⟨x, y, hx, hy, hxo, hyo, hxy, hyx⟩ := exists_commuting_pair_weight_two F
  refine one_le_pRank_ringChar_of_orderOf_eq ?_ hxo
  rw [Subgroup.mem_centralizer_iff]
  rintro h (rfl | rfl)
  · exact hx (Multiplicative.ofAdd ![1, 0, 0]) rfl
  · exact hx (Multiplicative.ofAdd ![0, 1, 0]) rfl

theorem one_le_pRank_centralizer_c₀_pair_u_e₂ [Finite K] (F : Frame K) :
    1 ≤ pRank (ringChar K)
      (Subgroup.centralizer ({c₀ F (Multiplicative.ofAdd ![1, 1, 1]),
        c₀ F (Multiplicative.ofAdd ![0, 0, 1])} : Set ↥(Omega7 K))) := by
  obtain ⟨x, y, hx, hy, hxo, hyo, hxy, hyx⟩ := exists_commuting_pair_weight_two F
  refine one_le_pRank_ringChar_of_orderOf_eq ?_ hyo
  rw [Subgroup.mem_centralizer_iff]
  rintro h (rfl | rfl)
  · exact hy (Multiplicative.ofAdd ![1, 1, 1]) rfl
  · exact hy (Multiplicative.ofAdd ![0, 0, 1]) rfl

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
