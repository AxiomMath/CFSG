module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryLattice
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace ProjectiveGeometry

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

theorem coe_inv_mul_coe (A : GL (Fin n) K) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem coe_mul_coe_inv (A : GL (Fin n) K) :
    (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem mulVecLin_bijective (A : GL (Fin n) K) :
    Function.Bijective (mulVecLin (A : Matrix (Fin n) (Fin n) K)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), fun v => ?_, fun v => ?_⟩
  · simp only [mulVecLin_apply, mulVec_mulVec, coe_inv_mul_coe, one_mulVec]
  · simp only [mulVecLin_apply, mulVec_mulVec, coe_mul_coe_inv, one_mulVec]

@[expose] noncomputable def glOrderIso (A : GL (Fin n) K) :
    Submodule K (Fin n → K) ≃o Submodule K (Fin n → K) :=
  Submodule.orderIsoMapComapOfBijective _ (mulVecLin_bijective A)

theorem glOrderIso_apply (A : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    glOrderIso A W = W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K)) :=
  rfl

theorem map_mulVecLin_inv_map (A : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    (W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))).map
      (mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = W := by
  rw [← Submodule.map_comp, ← mulVecLin_mul, coe_inv_mul_coe, mulVecLin_one, Submodule.map_id]

theorem map_mulVecLin_map_inv (A : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    (W.map (mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).map
      (mulVecLin (A : Matrix (Fin n) (Fin n) K)) = W := by
  rw [← Submodule.map_comp, ← mulVecLin_mul, coe_mul_coe_inv, mulVecLin_one, Submodule.map_id]

theorem map_span_singleton_mulVecLin (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (K ∙ v).map (mulVecLin M) = K ∙ (M *ᵥ v) := by
  rw [Submodule.map_span, Set.image_singleton, mulVecLin_apply]

theorem single_ne_zero (i : Fin n) : (Pi.single i (1 : K) : Fin n → K) ≠ 0 := fun h =>
  one_ne_zero (Pi.single_eq_zero_iff.mp h)

theorem iSup_span_single : ⨆ i : Fin n, K ∙ (Pi.single i (1 : K) : Fin n → K) = ⊤ := by
  rw [← Submodule.span_range_eq_iSup]
  convert (Pi.basisFun K (Fin n)).span_eq using 3
  ext j
  simp

theorem frame_normalization (Φ : Submodule K (Fin n → K) ≃o Submodule K (Fin n → K)) :
    ∃ A : GL (Fin n) K, ∃ Ψ : Submodule K (Fin n → K) ≃o Submodule K (Fin n → K),
      (∀ W, Ψ W = (Φ W).map (mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∧
      (∀ i : Fin n, Ψ (K ∙ Pi.single i 1) = K ∙ Pi.single i 1) ∧
      Ψ (K ∙ (1 : Fin n → K)) = K ∙ (1 : Fin n → K) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, Φ.trans (glOrderIso 1⁻¹), fun W => rfl, fun i => i.elim0, Subsingleton.elim _ _⟩
  have hpt : ∀ i : Fin n, ∃ v : Fin n → K, v ≠ 0 ∧ Φ (K ∙ Pi.single i 1) = K ∙ v := fun i =>
    exists_eq_span_singleton ((finrank_orderIso Φ _).trans (finrank_span_singleton
      (single_ne_zero i)))
  choose v hv0 hv using hpt
  have hspan : ⨆ i, K ∙ v i = ⊤ := by
    calc ⨆ i, K ∙ v i = ⨆ i, Φ (K ∙ Pi.single i 1) := by simp_rw [hv]
      _ = Φ (⨆ i, K ∙ Pi.single i 1) := (Φ.map_iSup _).symm
      _ = ⊤ := by rw [iSup_span_single, OrderIso.map_top]
  have hmem : ∀ u : Fin n → K, u ∈ Submodule.span K (Set.range v) := fun u => by
    rw [Submodule.span_range_eq_iSup, hspan]
    exact Submodule.mem_top
  have h1ne : (1 : Fin n → K) ≠ 0 := fun h => one_ne_zero (congrFun h ⟨0, hn⟩)
  obtain ⟨w, -, hw⟩ := exists_eq_span_singleton
    ((finrank_orderIso Φ (K ∙ (1 : Fin n → K))).trans (finrank_span_singleton h1ne))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hmem w)
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i hai
    set T := ⨆ (j : Fin n) (_ : j ≠ i), K ∙ (Pi.single j (1 : K) : Fin n → K) with hT
    have hT1 : (1 : Fin n → K) ∉ T := by
      intro h1
      have hle : T ≤ LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : Fin n => K) i) := by
        refine iSup₂_le fun j hj => ?_
        rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.proj_apply,
          Pi.single_eq_of_ne' hj]
      have := hle h1
      rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.one_apply] at this
      exact one_ne_zero this
    have hΦT : Φ T = ⨆ (j : Fin n) (_ : j ≠ i), K ∙ v j := by
      rw [hT, map_iSup₂]
      simp_rw [hv]
    have hwT : w ∈ Φ T := by
      rw [hΦT, ← ha]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hji : j = i
      · rw [hji, hai, zero_smul]
        exact Submodule.zero_mem _
      · exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hji
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    apply hT1
    have h1 : K ∙ w ≤ Φ T := (Submodule.span_singleton_le_iff_mem _ _).mpr hwT
    rw [← hw, Φ.le_iff_le] at h1
    exact (Submodule.span_singleton_le_iff_mem _ _).mp h1
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) K, A = Matrix.of fun r c => a c * v c r :=
    ⟨_, rfl⟩
  have hAcol : ∀ c, A *ᵥ Pi.single c 1 = a c • v c := fun c => by
    ext r
    rw [mulVec_single_one, hA]
    simp
  have hA1 : A *ᵥ (1 : Fin n → K) = w := by
    rw [← ha]
    ext r
    simp [hA, mulVec, dotProduct, Finset.sum_apply]
  have hAunit : IsUnit A := by
    rw [← mulVec_surjective_iff_isUnit]
    intro u
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hmem u)
    refine ⟨fun c => b c / a c, ?_⟩
    rw [← hb]
    ext r
    simp only [hA, mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    field_simp [ha0 c]
  set B : GL (Fin n) K := hAunit.unit with hB
  have hBA : (B : Matrix (Fin n) (Fin n) K) = A := hAunit.unit_spec
  have hBe : ∀ i, (K ∙ Pi.single i (1 : K)).map (mulVecLin (B : Matrix (Fin n) (Fin n) K)) =
      Φ (K ∙ Pi.single i 1) := fun i => by
    rw [map_span_singleton_mulVecLin, hBA, hAcol, Submodule.span_singleton_smul_eq
      (ha0 i).isUnit, hv]
  have hB1 : (K ∙ (1 : Fin n → K)).map (mulVecLin (B : Matrix (Fin n) (Fin n) K)) =
      Φ (K ∙ 1) := by
    rw [map_span_singleton_mulVecLin, hBA, hA1, hw]
  refine ⟨B, Φ.trans (glOrderIso B⁻¹), fun W => rfl, fun i => ?_, ?_⟩
  · change (Φ (K ∙ Pi.single i 1)).map
      (mulVecLin ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = _
    rw [← hBe i, map_mulVecLin_inv_map]
  · change (Φ (K ∙ 1)).map (mulVecLin ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = _
    rw [← hB1, map_mulVecLin_inv_map]

end ProjectiveGeometry

end CFSG.LocalAnalysis.ComponentInitial
