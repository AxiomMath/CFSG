module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalKron
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalKronOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K]

theorem rotMat_one_mulVec_vecOf_left (x : Fin 3 → K) :
    rotMat K ![1, 1, 1] *ᵥ vecOf K x 0 0 = vecOf K 0 x 0 := by
  rw [rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, rfl⟩ <;> fin_cases i <;>
    simp [planeRot_one]

theorem rotMat_one_mulVec_vecOf_mid (x : Fin 3 → K) :
    rotMat K ![1, 1, 1] *ᵥ vecOf K 0 x 0 = vecOf K (-x) (-x) 0 := by
  rw [rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, rfl⟩ <;> fin_cases i <;>
    simp [planeRot_one]

theorem commute_c₀_omegaRoot_isotropic [Finite K] (F : Frame K) {x : Fin 3 → K}
    (hxx : x ⬝ᵥ x = 0) :
    Commute (c₀ F (Multiplicative.ofAdd ![1, 1, 1]))
      (omegaRoot F (vecOf K x 0 0) (vecOf K 0 x 0)) := by
  have hQ1 : modelQuad K F.a (vecOf K x 0 0) = 0 := by
    rw [modelQuad_vecOf_eq_dotProduct]
    simp [hxx]
  have hQ2 : modelQuad K F.a (vecOf K 0 x 0) = 0 := by
    rw [modelQuad_vecOf_eq_dotProduct]
    simp [hxx]
  have hB : modelPolar K F.a (vecOf K x 0 0) (vecOf K 0 x 0) = 0 := by
    rw [modelPolar_vecOf_eq_dotProduct]
    simp [hxx]
  have hsum : vecOf K x 0 0 + vecOf K 0 x 0 + vecOf K (-x) (-x) 0 = 0 := by
    funext a
    rcases a with i | i | u <;> simp [vecOf]
  have h := omegaRoot_conj_c₀ F (Multiplicative.ofAdd ![1, 1, 1]) (vecOf K x 0 0) (vecOf K 0 x 0)
  rw [toAdd_ofAdd, rotMat_one_mulVec_vecOf_left, rotMat_one_mulVec_vecOf_mid,
    omegaRoot_cyclic F hsum hQ1 hQ2 hB] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem omegaRoot_isotropic_ne_one [Finite K] (F : Frame K) {x : Fin 3 → K} (hx0 : x ≠ 0)
    (hxx : x ⬝ᵥ x = 0) : omegaRoot F (vecOf K x 0 0) (vecOf K 0 x 0) ≠ 1 := by
  have hQ1 : modelQuad K F.a (vecOf K x 0 0) = 0 := by
    rw [modelQuad_vecOf_eq_dotProduct]
    simp [hxx]
  have hB : modelPolar K F.a (vecOf K x 0 0) (vecOf K 0 x 0) = 0 := by
    rw [modelPolar_vecOf_eq_dotProduct]
    simp [hxx]
  refine omegaRoot_ne_one_of_not_mem_span F hQ1 ?_ hB ?_
  · intro h
    apply hx0
    funext i
    simpa using congrFun h (.inl i)
  · intro c h
    apply hx0
    funext i
    simpa using (congrFun h (.inr (.inl i)))

theorem exists_commuting_pair_weight_three [Finite K] (F : Frame K) :
    ∃ x y : ↥(Omega7 K),
      Commute (c₀ F (Multiplicative.ofAdd ![1, 1, 1])) x ∧
      Commute (c₀ F (Multiplicative.ofAdd ![1, 1, 1])) y ∧
      orderOf x = ringChar K ∧ orderOf y = ringChar K ∧ Commute x y ∧
      y ∉ Subgroup.zpowers x := by
  obtain ⟨A, hA, hAo, x₀, hx0, hxx, hAx⟩ :=
    exists_orthogonal_orderOf_eq_ringChar_fixing_isotropic (K := K) F.hK
  have hodd : Odd (orderOf A) := by
    rw [hAo]
    exact (CharP.prime_ringChar K).odd_of_ne_two F.hK
  have hne := omegaRoot_isotropic_ne_one F hx0 hxx
  have hQ1 : modelQuad K F.a (vecOf K x₀ 0 0) = 0 := by
    rw [modelQuad_vecOf_eq_dotProduct]
    simp [hxx]
  have hQ2 : modelQuad K F.a (vecOf K 0 x₀ 0) = 0 := by
    rw [modelQuad_vecOf_eq_dotProduct]
    simp [hxx]
  have hB : modelPolar K F.a (vecOf K x₀ 0 0) (vecOf K 0 x₀ 0) = 0 := by
    rw [modelPolar_vecOf_eq_dotProduct]
    simp [hxx]
  have hone : (![1, 1, 1] : Fin 3 → ZMod 3) = fun _ => 1 := by
    funext i
    fin_cases i <;> rfl
  have hfix1 : kronMat (A : Matrix (Fin 3) (Fin 3) K) *ᵥ vecOf K x₀ 0 0 = vecOf K x₀ 0 0 := by
    rw [kronMat_mulVec_vecOf, hAx, Matrix.mulVec_zero]
  have hfix2 : kronMat (A : Matrix (Fin 3) (Fin 3) K) *ᵥ vecOf K 0 x₀ 0 = vecOf K 0 x₀ 0 := by
    rw [kronMat_mulVec_vecOf, hAx, Matrix.mulVec_zero]
  have hAA := modelQuad_kronGL_mulVec hA F.a
  refine ⟨omegaRoot F (vecOf K x₀ 0 0) (vecOf K 0 x₀ 0), kronElt F hA hodd,
    commute_c₀_omegaRoot_isotropic F hxx, ?_, orderOf_omegaRoot F hne,
    (orderOf_kronElt F hA hodd).trans hAo, ?_, ?_⟩
  · have h := commute_c₀_kronElt F hA hodd 1
    rwa [← hone] at h
  · have h := conj_omegaRootGL F (m := kronGL A) hAA (vecOf K x₀ 0 0) (vecOf K 0 x₀ 0)
    rw [coe_kronGL, hfix1, hfix2] at h
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · rintro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hBk : modelPolar K F.a (vecOf K x₀ 0 0) (k • vecOf K 0 x₀ 0) = 0 := by
      rw [← Int.cast_smul_eq_zsmul K, modelPolar_smul_right, hB, mul_zero]
    rw [omegaRoot_zpow F hB k] at hk
    obtain ⟨j, hj⟩ : ∃ j, x₀ j ≠ 0 := by simpa [Function.ne_iff] using hx0
    have hk' : omegaRootGL F (vecOf K x₀ 0 0) (k • vecOf K 0 x₀ 0) =
        F.P * kronGL A * F.P⁻¹ := congrArg (fun g : ↥(Omega7 K) => (g : GL Idx K)) hk
    have h1 := omegaRootGL_model_apply F hQ1 hBk (vecOf K (Pi.single j 1) 0 0)
    have h2 : ((F.P⁻¹ * omegaRootGL F (vecOf K x₀ 0 0) (k • vecOf K 0 x₀ 0) * F.P : GL Idx K) :
        Matrix Idx Idx K) *ᵥ vecOf K (Pi.single j 1) 0 0 =
        kronMat (A : Matrix (Fin 3) (Fin 3) K) *ᵥ vecOf K (Pi.single j 1) 0 0 := by
      rw [hk']
      have : F.P⁻¹ * (F.P * kronGL A * F.P⁻¹) * F.P = kronGL A := by group
      rw [this]
      rfl
    rw [h2, kronMat_mulVec_vecOf] at h1
    have h3 := congrFun h1 (.inr (.inl j))
    simp only [vecOf_inr_inl, Matrix.mulVec_zero, Pi.zero_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, modelPolar_vecOf_eq_dotProduct, single_dotProduct] at h3
    simp only [zero_dotProduct, dotProduct_zero, mul_zero, sub_zero, add_zero, zero_add, one_mul,
      zsmul_eq_mul] at h3
    have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero F.hK
    have hk0 : (k : K) = 0 := by
      rcases mul_eq_zero.mp h3.symm with h | h
      · exact absurd h (mul_ne_zero h2K hj)
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact absurd h hj
    have hz : k • vecOf K 0 x₀ 0 = 0 := by rw [← Int.cast_smul_eq_zsmul K, hk0, zero_smul]
    rw [hz, omegaRoot_zero_right] at hk
    have hord := orderOf_kronElt F hA hodd
    rw [← hk, orderOf_one, hAo] at hord
    exact absurd hord (CharP.prime_ringChar K).one_lt.ne

theorem two_le_pRank_centralizer_c₀_weight_three [Finite K] (F : Frame K) :
    2 ≤ pRank (ringChar K)
      (Subgroup.centralizer ({c₀ F (Multiplicative.ofAdd ![1, 1, 1])} : Set ↥(Omega7 K))) := by
  obtain ⟨x, y, hx, hy, hxo, hyo, hxy, hyx⟩ := exists_commuting_pair_weight_three F
  exact two_le_pRank_ringChar_of_commute (Subgroup.mem_centralizer_singleton_iff.mpr hx.symm)
    (Subgroup.mem_centralizer_singleton_iff.mpr hy.symm) hxo hyo hxy hyx

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
