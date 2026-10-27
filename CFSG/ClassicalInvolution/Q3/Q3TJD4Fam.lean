module

public import CFSG.ClassicalInvolution.Q3.Q3TJD4Spin
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Matrix Pointwise

variable {K : Type} [Field K]

variable (K) in
noncomputable abbrev d4Proj :
    spinGroup (quadPlus 4 K) →* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
  spinToStatedProj (quadPlus 4 K) (range_spinMatrix_quadPlus three_le_four)

theorem d4Proj_subspaceAction (x : spinGroup (quadPlus 4 K))
    (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (d4Proj K x) W =
      W.map (toLinEquiv _ K (spinMatrix (quadPlus 4 K) x)).toLinearMap := by
  rw [spinToStatedProj_apply]
  rfl

theorem quadPlus_mulVec_of_mem_statedOmega {g : GL (Fin 4 ⊕ Fin 4) K}
    (hg : g ∈ StatedOmega (StatedQuadPlus 4 K)) (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) = quadPlus 4 K v := by
  rw [statedOmega_eq_comap (coe_quadPlus 4 K), Subgroup.mem_comap] at hg
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    Subgroup.commutator_le.mpr fun a ha b hb => Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
      (Subgroup.inv_mem _ hb)
  have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hle hg) v
  simpa only [MulEquiv.coe_toMonoidHom, toLinEquiv_apply] using h

theorem map_span_eq_of_fix {V : Type*} [AddCommGroup V] [Module K V] (T : V →ₗ[K] V)
    (S : Set V) (h : ∀ v ∈ S, T v = v) : (Submodule.span K S).map T = Submodule.span K S := by
  rw [Submodule.map_span, Set.image_congr h, Set.image_id']

theorem d4Proj_d4Six_mem_firstPointStabilizer (i : Bool ⊕ Bool × Bool) :
    d4Proj K (d4Six K i) ∈ firstPointStabilizer (n := 4) (K := K) := by
  change statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (d4Proj K (d4Six K i))
    (flag 4 K 1) = flag 4 K 1
  rw [d4Proj_subspaceAction, flag]
  refine map_span_eq_of_fix _ _ ?_
  rintro _ ⟨j, hj, rfl⟩
  obtain rfl : j = 0 := Fin.ext (by simpa using hj)
  rw [LinearEquiv.coe_coe, toLinEquiv_apply, coe_spinMatrix_d4Six, Matrix.add_mulVec,
    Matrix.one_mulVec, d4SixMat_mulVec_e0, add_zero]

theorem not_forall_d4Proj_d4Six_fix (W : Submodule K (Fin 4 ⊕ Fin 4 → K))
    (hdim : Module.finrank K W = 4) (hts : ∀ v ∈ W, StatedQuadPlus 4 K v = 0)
    (u : StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (h : ∀ i, statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (d4Proj K (d4Six K i))
      (statedProjectiveSubspaceAction (StatedQuadPlus 4 K) u W) =
        statedProjectiveSubspaceAction (StatedQuadPlus 4 K) u W) : False := by
  obtain ⟨U, rfl⟩ := QuotientGroup.mk'_surjective _ u
  simp only [statedProjectiveSubspaceAction_mk_apply] at h
  set W' := W.map (toLinEquiv _ K U.val).toLinearMap with hW'
  have hts' : ∀ w ∈ W', quadPlus 4 K w = 0 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [LinearEquiv.coe_coe, toLinEquiv_apply, quadPlus_mulVec_of_mem_statedOmega U.2,
      coe_quadPlus]
    exact hts v hv
  have hdim' : Module.finrank K W' = 4 := by
    rw [hW', LinearEquiv.finrank_map_eq]
    exact hdim
  have hinv : ∀ i, ∀ w ∈ W', d4SixMat K i *ᵥ w ∈ W' := by
    intro i w hw
    have hmem : (spinMatrix (quadPlus 4 K) (d4Six K i) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ w ∈ W' := by
      have h' := h i
      rw [d4Proj_subspaceAction] at h'
      rw [← h']
      exact ⟨w, hw, rfl⟩
    rw [coe_spinMatrix_d4Six, Matrix.add_mulVec, Matrix.one_mulVec] at hmem
    have h2 := W'.sub_mem hmem hw
    rwa [add_sub_cancel_left] at h2
  have := finrank_le_three_of_d4SixMat W' hts' hinv
  omega

theorem smul_statedPointFamily_eq_of_fix [Finite K]
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
    (g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (hβ : ∀ i, β (g * d4Proj K (d4Six K i) * g⁻¹) = g * d4Proj K (d4Six K i) * g⁻¹) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  set P₀ := (firstPointStabilizer (n := 4) (K := K)).map (MulAut.conj g).toMonoidHom with hP₀
  have hP₀F : P₀ ∈ statedPointFamily (coe_quadPlus 4 K) := by
    rw [statedPointFamily_eq_conjugacyFamily three_le_four]
    exact ⟨g, rfl⟩
  have hmem : ∀ i, g * d4Proj K (d4Six K i) * g⁻¹ ∈ P₀.map β.toMonoidHom := fun i =>
    ⟨_, ⟨_, d4Proj_d4Six_mem_firstPointStabilizer i, rfl⟩, hβ i⟩
  have hexcl : ∀ W : Submodule K (Fin 4 ⊕ Fin 4 → K), Module.finrank K W = 4 →
      (∀ v ∈ W, StatedQuadPlus 4 K v = 0) → P₀.map β.toMonoidHom ∉
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W) := by
    rintro W hdim hts ⟨y, hy⟩
    refine not_forall_d4Proj_d4Six_fix W hdim hts (g⁻¹ * y) fun i => ?_
    have hi := hmem i
    rw [← hy] at hi
    obtain ⟨t, ht, hty⟩ := hi
    have hty' : y * t * y⁻¹ = g * d4Proj K (d4Six K i) * g⁻¹ := hty
    have ht' : statedProjectiveSubspaceAction (StatedQuadPlus 4 K) t W = W := ht
    have hxy : d4Proj K (d4Six K i) * (g⁻¹ * y) = (g⁻¹ * y) * t := by
      calc d4Proj K (d4Six K i) * (g⁻¹ * y) =
          g⁻¹ * (g * d4Proj K (d4Six K i) * g⁻¹) * y := by group
        _ = g⁻¹ * (y * t * y⁻¹) * y := by rw [hty']
        _ = (g⁻¹ * y) * t := by group
    rw [← Equiv.Perm.mul_apply, ← map_mul, hxy, map_mul, Equiv.Perm.mul_apply, ht']
  have hO := stated_pointFamily_orbit_subset (K := K) (n := 4) rfl (MulAction.mem_orbit _ β)
  have hP₀β : P₀.map β.toMonoidHom ∈ β • statedPointFamily (coe_quadPlus 4 K) :=
    Set.mem_smul_set.mpr ⟨P₀, hP₀F, rfl⟩
  rcases hO with h | h | h
  · exact h
  · rw [h] at hP₀β
    exact absurd hP₀β (hexcl _ (flag_data le_rfl).1 (flag_data le_rfl).2)
  · rw [h] at hP₀β
    exact absurd hP₀β (hexcl _ (Xstar_data three_le_four).1 (Xstar_data three_le_four).2)

end CFSG.ClassicalInvolution.Q3.Q3T
