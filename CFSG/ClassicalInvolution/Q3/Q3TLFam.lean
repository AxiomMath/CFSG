module

public import CFSG.ClassicalInvolution.Q3.Q3TLFix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
public import CFSG.ClassicalInvolution.Q3.Q3TJD4Fam

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Matrix Pointwise

variable {K : Type} [Field K]

theorem toLinEquiv_mem_orthogonalGroup {g : GL (Fin 4 ⊕ Fin 4) K}
    (hg : g ∈ StatedOmega (StatedQuadPlus 4 K)) :
    toLinEquiv _ K g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
    rw [toLinEquiv_apply]
    exact quadPlus_mulVec_of_mem_statedOmega hg v

theorem toLinEquiv_mem_elementaryGroup {g : GL (Fin 4 ⊕ Fin 4) K}
    (hg : g ∈ StatedOmega (StatedQuadPlus 4 K)) :
    toLinEquiv _ K g ∈ elementaryGroup (quadPlus 4 K) := by
  rw [statedOmega_eq_comap (coe_quadPlus 4 K), Subgroup.mem_comap,
    commutator_orthogonalGroup_quadPlus (by omega)] at hg
  exact hg

theorem symm_mem_statedOmega {a : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (ha : a ∈ elementaryGroup (quadPlus 4 K)) :
    (toLinEquiv _ K).symm a ∈ StatedOmega (StatedQuadPlus 4 K) := by
  rw [statedOmega_eq_comap (coe_quadPlus 4 K), Subgroup.mem_comap,
    commutator_orthogonalGroup_quadPlus (by omega)]
  change toLinEquiv _ K ((toLinEquiv _ K).symm a) ∈ _
  rw [MulEquiv.apply_symm_apply]
  exact ha

theorem mk_mem_stabilizer_iff (g : StatedOmega (StatedQuadPlus 4 K))
    (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    (QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K))) ∈
        statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W ↔
      W.map (toLinEquiv _ K g.val).toLinearMap = W :=
  Iff.rfl

theorem fixFam_point_of_le {w : Fin 4 ⊕ Fin 4 → K} (hw0 : w ≠ 0) (hw : quadPlus 4 K w = 0)
    {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (hH : H ≤ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (K ∙ w)) :
    FixFam (statedPointFamily (coe_quadPlus 4 K)) H := by
  have hL : Module.finrank K (K ∙ w) = 1 ∧ ∀ x ∈ (K ∙ w), quadPlus 4 K x = 0 := by
    refine ⟨finrank_span_singleton hw0, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [QuadraticMap.map_smul, hw, smul_zero]
  let L : Points (quadPlus 4 K) := ⟨K ∙ w, hL⟩
  refine ⟨statedPointStabilizer (coe_quadPlus 4 K) L, ⟨L, rfl⟩, ?_⟩
  rw [statedPointStabilizer_eq_subspaceStabilizer]
  exact hH

theorem exists_of_fixFam_point {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (h : FixFam (statedPointFamily (coe_quadPlus 4 K)) H) :
    ∃ w : Fin 4 ⊕ Fin 4 → K, w ≠ 0 ∧ quadPlus 4 K w = 0 ∧
      H ≤ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (K ∙ w) := by
  obtain ⟨M, ⟨⟨Lsub, hLdim, hLsing⟩, rfl⟩, hHM⟩ := h
  have hHM' : H ≤ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) Lsub := by
    have h1 := statedPointStabilizer_eq_subspaceStabilizer (n := 4) (K := K)
      ⟨Lsub, hLdim, hLsing⟩
    intro x hx
    have h2 := hHM hx
    change x ∈ statedPointStabilizer (coe_quadPlus 4 K) ⟨Lsub, hLdim, hLsing⟩ at h2
    rw [h1] at h2
    exact h2
  obtain ⟨w, hw0, hLw⟩ := finrank_eq_one_iff'.mp hLdim
  have hspan : Lsub = K ∙ (w : Fin 4 ⊕ Fin 4 → K) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨c, hc⟩ := hLw ⟨x, hx⟩
      rw [show x = c • (w : Fin 4 ⊕ Fin 4 → K) from (congrArg Subtype.val hc).symm]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact w.2
  refine ⟨w, fun h => hw0 (Subtype.ext h), hLsing w w.2, ?_⟩
  rw [← hspan]
  exact hHM'

theorem exists_of_fixFam_solid {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (h : FixFam (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4))) H) :
    ∃ S ∈ singularSubspaces (quadPlus 4 K) 4,
      H ≤ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) S := by
  obtain ⟨M, ⟨u, rfl⟩, hHM⟩ := h
  change H ≤ (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)).map
    (MulAut.conj u).toMonoidHom at hHM
  rw [statedProjectiveSubspaceStabilizer_map_conj] at hHM
  refine ⟨_, ?_, hHM⟩
  obtain ⟨U, rfl⟩ := QuotientGroup.mk'_surjective _ u
  rw [statedProjectiveSubspaceAction_mk_apply]
  exact map_mem_singularSubspaces (toLinEquiv_mem_orthogonalGroup U.2)
    (flag_mem_singularSubspaces le_rfl)

theorem fixFam_solid_of_le [Finite K] {S : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hS : S ∈ singularSubspaces (quadPlus 4 K) 4)
    {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (hH : H ≤ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) S) :
    FixFam (conjugacyFamily
        (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4))) H ∨
      FixFam (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
        (Xstar 4 K (by omega)))) H := by
  have key : ∀ X : Submodule K (Fin 4 ⊕ Fin 4 → K),
      S ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K)) X →
        FixFam (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) X)) H := by
    intro X hX
    obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.mp hX
    set u : StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
      QuotientGroup.mk ⟨(toLinEquiv _ K).symm a, symm_mem_statedOmega ha⟩ with hu
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    change H ≤ (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) X).map
      (MulAut.conj u).toMonoidHom
    rw [statedProjectiveSubspaceStabilizer_map_conj, hu]
    change H ≤ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
      (X.map (toLinEquiv _ K ((toLinEquiv _ K).symm a)).toLinearMap)
    rw [MulEquiv.apply_symm_apply]
    exact hH
  rcases (orthogonal_geometry_split_maximal_family_orbits (K := K) (r := 4) (by omega)).2.2.2.2.1
    S hS with h | h
  · exact Or.inl (key _ h)
  · exact Or.inr (key _ h)

end CFSG.ClassicalInvolution.Q3.Q3T
