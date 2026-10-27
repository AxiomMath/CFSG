module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryAffine
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace ProjectiveGeometry

open Module LinearFlag

variable {K : Type*} [Field K] {n d : ℕ}

theorem coordImage_symm_coordImage (σ : K ≃+* K) (W : Submodule K (Fin n → K)) :
    coordImage σ.symm (coordImage σ W) = W := by
  ext v
  simp [mem_coordImage]

theorem coordImage_coordImage_symm (σ : K ≃+* K) (W : Submodule K (Fin n → K)) :
    coordImage σ (coordImage σ.symm W) = W := by
  ext v
  simp [mem_coordImage]

@[expose] noncomputable def coordImageOrderIso (σ : K ≃+* K) :
    Submodule K (Fin n → K) ≃o Submodule K (Fin n → K) where
  toFun := coordImage σ
  invFun := coordImage σ.symm
  left_inv := coordImage_symm_coordImage σ
  right_inv := coordImage_coordImage_symm σ
  map_rel_iff' {W W'} := by
    change coordImage σ W ≤ coordImage σ W' ↔ W ≤ W'
    constructor
    · intro h w hw
      have := h (coord_mem_coordImage hw)
      rw [mem_coordImage] at this
      simpa using this
    · intro h v hv
      rw [mem_coordImage] at hv ⊢
      exact h hv

theorem coordImageOrderIso_apply (σ : K ≃+* K) (W : Submodule K (Fin n → K)) :
    coordImageOrderIso σ W = coordImage σ W :=
  rfl

theorem coordImage_span_singleton (σ : K ≃+* K) (v : Fin n → K) :
    coordImage σ (K ∙ v) = K ∙ fun i => σ (v i) := by
  ext w
  rw [mem_coordImage, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨σ c, funext fun i => ?_⟩
    have h := congrFun hc i
    simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
    rw [← map_mul, h, RingEquiv.apply_symm_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨σ.symm c, funext fun i => ?_⟩
    simp

theorem coord_extend (σ : K ≃+* K) (x : Fin d → K) (c : K) :
    (fun i => σ (extend x c i)) = extend (fun i => σ (x i)) (σ c) :=
  extend_ext (fun i => by simp) (by simp)

theorem infinity_extension (σ : K ≃+* K)
    (Ψ : Submodule K (Fin (d + 1) → K) ≃o Submodule K (Fin (d + 1) → K))
    (hΨa : ∀ x : Fin d → K, Ψ (affinePoint x) = affinePoint fun i => σ (x i))
    (hΨH : Ψ (infinityHyperplane d K) = infinityHyperplane d K) :
    ∀ W : Submodule K (Fin (d + 1) → K), Ψ W = coordImage σ W := by
  have hpt : ∀ L : Submodule K (Fin (d + 1) → K), finrank K L = 1 →
      Ψ L = coordImageOrderIso σ L := by
    intro L hL
    rw [coordImageOrderIso_apply]
    rcases point_cases hL with ⟨x, rfl⟩ | ⟨u, -, rfl⟩
    · rw [hΨa, affinePoint, affinePoint, coordImage_span_singleton, coord_extend, map_one]
    · have h1 : infinityPoint u = (affinePoint 0 ⊔ affinePoint u) ⊓ infinityHyperplane d K := by
        rw [affinePoint_sup, sub_zero, projLine_inf]
      have h2 : (fun i => σ ((0 : Fin d → K) i)) = 0 := funext fun i => by simp
      have hΨu : Ψ (infinityPoint u) = infinityPoint fun i => σ (u i) := by
        rw [h1, Ψ.map_inf, Ψ.map_sup, hΨa, hΨa, hΨH, h2, affinePoint_sup, sub_zero, projLine_inf]
      rw [hΨu, infinityPoint, infinityPoint, coordImage_span_singleton, coord_extend, map_zero]
  intro W
  rw [orderIso_eq_of_forall_point Ψ (coordImageOrderIso σ) hpt]
  rfl

end ProjectiveGeometry

end CFSG.LocalAnalysis.ComponentInitial
