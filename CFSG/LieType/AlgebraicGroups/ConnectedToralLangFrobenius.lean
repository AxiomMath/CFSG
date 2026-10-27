module

public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

theorem frobTwistCoGL_mem_subgroupPoints
    (e : ℕ) (Q : ModGL τ k) {Z : Subgroup (ModGL τ k)}
    (hQ : ∀ g ∈ Z, frobTwistGL τ k p e Q g ∈ Z) :
    ∀ y ∈ subgroupPoints (Z.map (modGLPoint τ k).toMonoidHom),
      y.comp (frobTwistCoGL p e Q) ∈ subgroupPoints (Z.map (modGLPoint τ k).toMonoidHom) := by
  intro y hy
  rw [subgroupPoints_map] at hy ⊢
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨frobTwistGL τ k p e Q g, hQ g hg, ?_⟩
  have h := modGLPoint_symm_comp_frobTwistCoGL p e Q (modGLPoint τ k g).ofConv
  rw [toConv_ofConv, MulEquiv.symm_apply_apply] at h
  beta_reduce
  rw [← h, MulEquiv.apply_symm_apply, ofConv_toConv]

variable [IsAlgClosed k]

theorem exists_frobTwist_restriction {Z : Subgroup (ModGL τ k)}
    (hZ : IsConnectedAlgebraicSubgroup k (Z.map (modGLPoint τ k).toMonoidHom)) {e : ℕ}
    (he : 1 ≤ e) (Q : ModGL τ k) (hQ : ∀ g ∈ Z, frobTwistGL τ k p e Q g ∈ Z) :
    ∃ σ : (GLCoord k (Label τ) ⧸ subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom)) →ₐc[k]
        (GLCoord k (Label τ) ⧸ subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom)),
      (∀ φ, (modGLPoint τ k).symm (toConv ((pointMap σ φ).ofConv.comp
          (Ideal.Quotient.mkₐ k _))) =
        frobTwistGL τ k p e Q
          ((modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))))) ∧
      (∀ D ∈ tangentSpace k _ (Bialgebra.counitAlgHom k
          (GLCoord k (Label τ) ⧸ subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom))),
        D ∘ₗ (σ : (GLCoord k (Label τ) ⧸ subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom)) →ₐ[k]
          (GLCoord k (Label τ) ⧸ subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom))).toLinearMap =
            0) ∧
      ∀ c ∈ Z, ∃ z ∈ Z, z⁻¹ * frobTwistGL τ k p e Q z = c := by
  set H := Z.map (modGLPoint τ k).toMonoidHom with hH
  have := hZ.finiteType
  have := hZ.isReduced
  have hmem := frobTwistCoGL_mem_subgroupPoints p e Q hQ
  set σ := bialgHomOfPointMul (quotientCo H (frobTwistCoGL p e Q) hmem)
    (quotientCo_pointMul H _ hmem (frobTwistCoGL_pointMul p e Q)) with hσ
  have hpt : ∀ φ : WithConv ((GLCoord k (Label τ) ⧸ subgroupIdeal H) →ₐ[k] k),
      (modGLPoint τ k).symm (toConv ((pointMap σ φ).ofConv.comp (Ideal.Quotient.mkₐ k _))) =
        frobTwistGL τ k p e Q
          ((modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _)))) := by
    intro φ
    rw [pointMap_apply, ofConv_toConv, hσ, coe_bialgHomOfPointMul, comp_quotientCo_comp_mkₐ,
      modGLPoint_symm_comp_frobTwistCoGL]
  have hzero : ∀ D ∈ tangentSpace k _ (Bialgebra.counitAlgHom k
      (GLCoord k (Label τ) ⧸ subgroupIdeal H)),
      D ∘ₗ (σ : (GLCoord k (Label τ) ⧸ subgroupIdeal H) →ₐ[k]
        (GLCoord k (Label τ) ⧸ subgroupIdeal H)).toLinearMap = 0 := by
    intro D hD
    set π := Ideal.Quotient.mkₐ k (subgroupIdeal H)
    have hDπ : D ∘ₗ π.toLinearMap ∈
        tangentSpace k (GLCoord k (Label τ)) ((Bialgebra.counitAlgHom k _).comp π) :=
      (tangentMap π rfl ⟨D, hD⟩).2
    have h0 := tangent_comp_frobCo p he hDπ
    refine LinearMap.ext fun b => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ b
    have h1 := congrArg (fun f : GLCoord k (Label τ) →ₗ[k] k =>
      f (innerCo (modGLPoint τ k Q) a)) h0
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply] at h1
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply, hσ,
      coe_bialgHomOfPointMul]
    change D (quotientCo _ _ _ (π a)) = 0
    rw [← AlgHom.comp_apply (quotientCo _ _ _) π, quotientCo_comp_mkₐ, AlgHom.comp_apply,
      frobTwistCoGL, AlgHom.comp_apply]
    exact h1
  refine ⟨σ, hpt, hzero, fun c hc => ?_⟩
  have := hZ.smooth.1
  have := hZ.connectedSpace
  set eZ := (subgroupQuotientPointsEquiv H hZ.pointsZero_eq).trans
    ((modGLPoint τ k).subgroupMap Z).symm with heZ
  have heZv : ∀ φ, ((eZ φ : Z) : ModGL τ k) =
      (modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) := fun _ => rfl
  obtain ⟨h, hh⟩ := exceptional_Lang_connected_twisted_orbit_surjectivity σ le_rfl
    (fun D hD => by rw [pow_one]; exact hzero D hD) (eZ.symm ⟨c, hc⟩)
  refine ⟨eZ h, (eZ h).2, ?_⟩
  have h1 := congrArg (fun x => ((eZ x : Z) : ModGL τ k)) hh
  simp only [MulEquiv.apply_symm_apply, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  rw [h1, heZv (pointMap σ h), hpt, ← heZv]

end CFSG.LieType.AlgebraicGroups
