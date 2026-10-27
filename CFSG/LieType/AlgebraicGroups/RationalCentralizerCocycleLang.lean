module

public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagram
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv Topology

open scoped CFSG.ConvolutionPoints

section Lang

variable {τ : Tag} {k : Type} [Field k]

theorem mem_subgroupPoints_map_modGLPoint {H : Subgroup (ModGL τ k)}
    {y : GLCoord k (Label τ) →ₐ[k] k} :
    y ∈ subgroupPoints (H.map (modGLPoint τ k).toMonoidHom) ↔
      (modGLPoint τ k).symm (toConv y) ∈ H := by
  rw [subgroupPoints_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rwa [toConv_ofConv, MulEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, by simp only [MulEquiv.apply_symm_apply, ofConv_toConv]⟩

variable (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]

theorem tangent_comp_quotientCo_frobTwistCoGL
    {e : ℕ} (he : 1 ≤ e) (Q : ModGL τ k)
    (Hp : Subgroup (WithConv (GLCoord k (Label τ) →ₐ[k] k)))
    (hφ : ∀ y ∈ subgroupPoints Hp, y.comp (frobTwistCoGL p e Q) ∈ subgroupPoints Hp)
    {Dt : (GLCoord k (Label τ) ⧸ subgroupIdeal Hp) →ₗ[k] k}
    (hDt : Dt ∈ tangentSpace k (GLCoord k (Label τ) ⧸ subgroupIdeal Hp)
      (Bialgebra.counitAlgHom k _)) :
    Dt ∘ₗ (quotientCo Hp (frobTwistCoGL p e Q) hφ).toLinearMap = 0 := by
  set π := Ideal.Quotient.mkₐ k (subgroupIdeal Hp)
  have hDπ : Dt ∘ₗ π.toLinearMap ∈
      tangentSpace k (GLCoord k (Label τ)) ((Bialgebra.counitAlgHom k _).comp π) :=
    (tangentMap π rfl ⟨Dt, hDt⟩).2
  have h0 := tangent_comp_frobCo p he hDπ
  refine LinearMap.ext fun b => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ b
  have h1 := congrArg (fun f : GLCoord k (Label τ) →ₗ[k] k =>
    f (innerCo (modGLPoint τ k Q) a)) h0
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply] at h1
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply]
  change Dt (quotientCo _ _ _ (π a)) = 0
  rw [← AlgHom.comp_apply (quotientCo _ _ _) π, quotientCo_comp_mkₐ, AlgHom.comp_apply,
    frobTwistCoGL, AlgHom.comp_apply]
  exact h1

theorem exists_eq_inv_mul_frobTwistGL
    {e : ℕ} (he : 1 ≤ e) (Q : ModGL τ k)
    {M : Subgroup (ModGL τ k)}
    (hM : IsConnectedAlgebraicSubgroup k (M.map (modGLPoint τ k).toMonoidHom))
    (hsm : Algebra.Smooth k
      (GLCoord k (Label τ) ⧸ subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom)))
    (hMS : ∀ g ∈ M, frobTwistGL τ k p e Q g ∈ M) {m : ModGL τ k} (hm : m ∈ M) :
    ∃ z ∈ M, m = z⁻¹ * frobTwistGL τ k p e Q z := by
  set Mp := M.map (modGLPoint τ k).toMonoidHom with hMp
  have hφ : ∀ y ∈ subgroupPoints Mp, y.comp (frobTwistCoGL p e Q) ∈ subgroupPoints Mp := by
    intro y hy
    rw [mem_subgroupPoints_map_modGLPoint] at hy ⊢
    rw [modGLPoint_symm_comp_frobTwistCoGL]
    exact hMS _ hy
  have := hM.isReduced
  have := hM.connectedSpace
  let σ := bialgHomOfPointMul (quotientCo Mp (frobTwistCoGL p e Q) hφ)
    (quotientCo_pointMul Mp _ hφ (frobTwistCoGL_pointMul p e Q))
  let eM := (subgroupQuotientPointsEquiv Mp hM.pointsZero_eq).trans
    ((modGLPoint τ k).subgroupMap M).symm
  have heM : ∀ ψ, ((eM ψ : M) : ModGL τ k) =
      (modGLPoint τ k).symm (toConv (ψ.ofConv.comp (Ideal.Quotient.mkₐ k _))) := fun _ => rfl
  have hpm : ∀ ψ, ((eM (pointMap σ ψ) : M) : ModGL τ k) = frobTwistGL τ k p e Q (eM ψ) := by
    intro ψ
    rw [heM, heM, pointMap_apply, ofConv_toConv]
    have e1 : (ψ.ofConv.comp (σ : _ →ₐ[k] _)).comp (Ideal.Quotient.mkₐ k (subgroupIdeal Mp)) =
        (ψ.ofConv.comp (Ideal.Quotient.mkₐ k _)).comp (frobTwistCoGL p e Q) :=
      comp_quotientCo_comp_mkₐ Mp (frobTwistCoGL p e Q) hφ ψ.ofConv
    rw [e1]
    exact modGLPoint_symm_comp_frobTwistCoGL p e Q _
  obtain ⟨h, hh⟩ := exceptional_Lang_connected_twisted_orbit_surjectivity σ (le_refl 1)
    (fun Dt hDt => by
      rw [pow_one]
      exact tangent_comp_quotientCo_frobTwistCoGL p he Q Mp hφ hDt)
    (eM.symm ⟨m, hm⟩)
  refine ⟨eM h, (eM h).2, ?_⟩
  have h2 := congrArg (fun w => ((eM w : M) : ModGL τ k)) hh
  simp only [MulEquiv.apply_symm_apply, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_inv] at h2
  rw [h2, hpm]

omit [IsAlgClosed k] in
theorem frobTwistGL_mem_of_connectedComponentIn
    (e : ℕ) (Q : ModGL τ k)
    {Z M : Subgroup (ModGL τ k)}
    (hM : IsConnectedAlgebraicSubgroup k (M.map (modGLPoint τ k).toMonoidHom))
    (hZM : connectedComponentIn (PrimeSpectrum.zeroLocus
        (subgroupIdeal (Z.map (modGLPoint τ k).toMonoidHom) : Set (GLCoord k (Label τ))))
        (pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv) =
      PrimeSpectrum.zeroLocus
        (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom) : Set (GLCoord k (Label τ))))
    (hMZ : ∀ g ∈ M, frobTwistGL τ k p e Q g ∈ Z) {g : ModGL τ k} (hg : g ∈ M) :
    frobTwistGL τ k p e Q g ∈ M := by
  set Mp := M.map (modGLPoint τ k).toMonoidHom
  set Zp := Z.map (modGLPoint τ k).toMonoidHom
  set φ := frobTwistCoGL p e Q
  set Y := PrimeSpectrum.comap (φ : GLCoord k (Label τ) →+* GLCoord k (Label τ)) ''
    (pointSpec '' subgroupPoints Mp)
  have hirr : IsIrreducible (pointSpec '' subgroupPoints Mp) :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.2 hM.isPrime
  have hY : IsIrreducible Y := hirr.image _ (PrimeSpectrum.continuous_comap _).continuousOn
  have h1 : pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv ∈ Y := by
    refine ⟨pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv,
      ⟨_, Mp.one_mem, rfl⟩, ?_⟩
    rw [comap_pointSpec]
    congr 1
    exact congrArg ofConv (one_comp_of_pointMul φ (frobTwistCoGL_pointMul p e Q))
  have hYZ : Y ⊆ PrimeSpectrum.zeroLocus (subgroupIdeal Zp : Set (GLCoord k (Label τ))) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [comap_pointSpec, pointSpec_mem_zeroLocus]
    refine subset_pointsZero_pointsIdeal _ ?_
    rw [mem_subgroupPoints_map_modGLPoint] at hy ⊢
    rw [modGLPoint_symm_comp_frobTwistCoGL]
    exact hMZ _ hy
  have hYM := hY.2.isPreconnected.subset_connectedComponentIn h1 hYZ
  rw [hZM] at hYM
  have hy : (modGLPoint τ k g).ofConv ∈ subgroupPoints Mp := by
    rw [mem_subgroupPoints_map_modGLPoint, toConv_ofConv, MulEquiv.symm_apply_apply]
    exact hg
  have := hYM ⟨_, ⟨_, hy, rfl⟩, rfl⟩
  rw [comap_pointSpec, pointSpec_mem_zeroLocus, hM.pointsZero_eq,
    mem_subgroupPoints_map_modGLPoint, modGLPoint_symm_comp_frobTwistCoGL, toConv_ofConv,
    MulEquiv.symm_apply_apply] at this
  exact this

end Lang

end CFSG.LieType.AlgebraicGroups
