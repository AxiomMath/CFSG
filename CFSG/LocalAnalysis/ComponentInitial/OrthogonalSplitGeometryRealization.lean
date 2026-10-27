module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryOpposite

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)

variable {r : ℕ} {K : Type*} [Field K]

theorem splitScale_mul (c d : K) (v : Fin r ⊕ Fin r → K) :
    splitScale r K c (splitScale r K d v) = splitScale r K (c * d) v := by
  funext x
  rcases x with i | i
  · simp
  · simp [mul_assoc]

theorem splitScale_one (v : Fin r ⊕ Fin r → K) : splitScale r K 1 v = v := by
  funext x
  rcases x with i | i <;> simp

variable (r K) in
@[expose] noncomputable def splitScaleEquiv {c : K} (hc : c ≠ 0) :
    (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  LinearEquiv.ofLinearMap (splitScale r K c) (splitScale r K c⁻¹)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, splitScale_mul, mul_inv_cancel₀ hc, splitScale_one,
        LinearMap.id_apply])
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, splitScale_mul, inv_mul_cancel₀ hc, splitScale_one,
        LinearMap.id_apply])

theorem coe_splitScaleEquiv {c : K} (hc : c ≠ 0) :
    ((splitScaleEquiv r K hc : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) : (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      splitScale r K c :=
  rfl

theorem sCoord_splitScale (σ : K ≃+* K) (c : K) (v : Fin r ⊕ Fin r → K) :
    sCoord σ (splitScale r K c v) = splitScale r K (σ c) (sCoord σ v) := by
  funext x
  rcases x with i | i <;> simp [map_mul]

theorem sCoordImage_map_splitScale (σ : K ≃+* K) (c : K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    sCoordImage σ (W.map (splitScale r K c)) = (sCoordImage σ W).map (splitScale r K (σ c)) := by
  ext v
  rw [mem_sCoordImage, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    refine ⟨sCoord σ w, sCoord_mem_sCoordImage.2 hw, ?_⟩
    rw [← sCoord_splitScale, hwv, sCoord_sCoord_symm]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨sCoord σ.symm u, hu, ?_⟩
    rw [sCoord_splitScale, RingEquiv.symm_apply_apply]


theorem orthogonal_geometry_split_polar_realization {K : Type*} [Field K] {r : ℕ} (hr : 3 ≤ r)
    (φ : Points (quadPlus r K) ≃ Points (quadPlus r K))
    (hφ : ∀ L M : Points (quadPlus r K),
      PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (φ L).val (φ M).val) :
    ∃ (A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (σ : K ≃+* K) (μ : K), μ ≠ 0 ∧
      (∀ v, quadPlus r K (A (sCoord σ v)) = μ * σ (quadPlus r K v)) ∧
      ∀ L : Points (quadPlus r K), (φ L).val = semiImage A σ L.val := by
  obtain ⟨σ, A₁, hA₁, -, hT⟩ := orthogonal_geometry_split_opposite_normalization hr φ hφ
  set φ' := φ.trans (semiPointEquiv σ hA₁).symm with hφ'def
  have hφ' := polarOrtho_trans_symm σ hA₁ φ hφ
  have hfix : ∀ L : Points (quadPlus r K), (L.val ≤ flag r K r ∨ L.val ≤ ySpan r K) →
      φ' L = L := fun L hL => Subtype.ext (by
        rw [hφ'def, Equiv.trans_apply, coe_semiPointEquiv_symm, hT L hL, semiPreimage_semiImage])
  obtain ⟨c, hc, -, hD, -⟩ := orthogonal_geometry_split_point_rigidity hr φ' hφ'
    (fun L hL => hfix L (Or.inl hL)) (fun L hL => hfix L (Or.inr hL))
  have hσc : σ c ≠ 0 := (map_ne_zero σ).2 hc
  refine ⟨A₁ * splitScaleEquiv r K hσc, σ, σ c, hσc, fun v => ?_, fun L => ?_⟩
  · rw [LinearEquiv.mul_apply, map_of_mem hA₁]
    change quadPlus r K (splitScale r K (σ c) (sCoord σ v)) = _
    rw [quadPlus_splitScale, quadPlus_sCoord]
  · have h1 : (φ L).val = semiImage A₁ σ (φ' L).val := by
      rw [hφ'def, Equiv.trans_apply, coe_semiPointEquiv_symm, semiImage_semiPreimage]
    rw [h1, hD, semiImage, sCoordImage_map_splitScale, semiImage, ← Submodule.map_comp]
    rfl

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
