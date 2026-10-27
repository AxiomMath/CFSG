module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoO

public noncomputable section

namespace CFSG.AGLEmbedding.TrialityTwo

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open scoped Pointwise

variable {K : Type} [Field K]

theorem mk'_injective_of_card_eq_two (hK : Nat.card K = 2) :
    Function.Injective (QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
      (StatedOmega (StatedQuadPlus 4 K)))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk',
    CFSG.AGLEmbedding.statedScalars_index_eq_bot_of_card_eq_two hK, Subgroup.bot_subgroupOf]

@[expose] def omegaProjEquiv (hK : Nat.card K = 2) :
    StatedOmega (StatedQuadPlus 4 K) ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _)
    ⟨mk'_injective_of_card_eq_two hK, QuotientGroup.mk'_surjective _⟩

theorem omegaProjEquiv_apply (hK : Nat.card K = 2) (g : StatedOmega (StatedQuadPlus 4 K)) :
    omegaProjEquiv hK g = QuotientGroup.mk' _ g := rfl

theorem statedProjectiveSubspaceStabilizer_map_conj
    (c : StatedProj (StatedOmega (StatedQuadPlus 4 K))) (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W).map (MulAut.conj c).toMonoidHom =
      statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
        (statedProjectiveSubspaceAction (StatedQuadPlus 4 K) c W) :=
  CFSG.ComponentClassification.CatalogueBStabilizerFamily.pointStabilizer_conj
    (statedProjectiveSubspaceAction (StatedQuadPlus 4 K)) c W

theorem toLinEquiv_mem_orthogonalGroup (g : StatedOmega (StatedQuadPlus 4 K)) :
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 4 ⊕ Fin 4) K g.val ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
  have hg := (CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (coe_quadPlus 4 K)).le g.2
  exact Subgroup.commutator_le_self _ (Subgroup.mem_comap.mp hg)

theorem statedProjectiveSubspaceAction_mem_singularSubspaces
    (c : StatedProj (StatedOmega (StatedQuadPlus 4 K))) {W : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hW : W ∈ singularSubspaces (quadPlus 4 K) 4) :
    statedProjectiveSubspaceAction (StatedQuadPlus 4 K) c W ∈
      singularSubspaces (quadPlus 4 K) 4 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ c
  rw [statedProjectiveSubspaceAction_mk_apply]
  exact map_mem_singularSubspaces (toLinEquiv_mem_orthogonalGroup g) hW

theorem mem_statedPointFamily_iff (Y : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) :
    Y ∈ statedPointFamily (coe_quadPlus 4 K) ↔
      ∃ W, IsSingularPoint W ∧ Y = statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W := by
  constructor
  · rintro ⟨L, rfl⟩
    refine ⟨L.val, ⟨L.2.1, fun v hv => ?_⟩, statedPointStabilizer_eq_subspaceStabilizer L⟩
    rw [← coe_quadPlus]
    exact L.2.2 v hv
  · rintro ⟨W, ⟨hW1, hW2⟩, rfl⟩
    refine ⟨⟨W, hW1, fun v hv => ?_⟩, statedPointStabilizer_eq_subspaceStabilizer _⟩
    rw [coe_quadPlus]
    exact hW2 v hv

theorem exists_mk'_apply_eq [Finite K] {a : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (ha : a ∈ orthElementaryGroup (quadPlus 4 K)) (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    ∃ c : StatedProj (StatedOmega (StatedQuadPlus 4 K)),
      statedProjectiveSubspaceAction (StatedQuadPlus 4 K) c W = a • W := by
  have hE := CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (n := 4) (K := K)
    (by norm_num)
  set g := (CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv (coe_quadPlus 4 K) hE).symm ⟨a, ha⟩
  have hg := CFSG.ClassicalGroups.Orthogonal.coe_statedOmegaEquiv (coe_quadPlus 4 K) hE g
  rw [MulEquiv.apply_symm_apply] at hg
  refine ⟨QuotientGroup.mk' _ g, ?_⟩
  rw [statedProjectiveSubspaceAction_mk_apply, ← hg]
  rfl

theorem mem_solidFamilies_iff [Finite K]
    (Y : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) :
    (Y ∈ conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)) ∨
        Y ∈ conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (Xstar 4 K (by norm_num)))) ↔
      ∃ W ∈ singularSubspaces (quadPlus 4 K) 4,
        Y = statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W := by
  constructor
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, statedProjectiveSubspaceAction_mem_singularSubspaces c
        (flag_mem_singularSubspaces le_rfl), statedProjectiveSubspaceStabilizer_map_conj c _⟩
    · exact ⟨_, statedProjectiveSubspaceAction_mem_singularSubspaces c
        (Xstar_mem_singularSubspaces (by norm_num)),
        statedProjectiveSubspaceStabilizer_map_conj c _⟩
  · rintro ⟨W, hW, rfl⟩
    obtain ⟨-, -, -, -, hcover, -⟩ :=
      orthogonal_geometry_split_maximal_family_orbits (K := K) (r := 4) (by norm_num)
    rcases hcover W hW with hW' | hW'
    · obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hW'
      obtain ⟨c, hc⟩ := exists_mk'_apply_eq ha (flag 4 K 4)
      exact Or.inl ⟨c, (statedProjectiveSubspaceStabilizer_map_conj c _).trans (congrArg _ hc)⟩
    · obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hW'
      obtain ⟨c, hc⟩ := exists_mk'_apply_eq ha (Xstar 4 K (by norm_num))
      exact Or.inr ⟨c, (statedProjectiveSubspaceStabilizer_map_conj c _).trans (congrArg _ hc)⟩

theorem exists_mem_statedPointFamily_iff (g : StatedOmega (StatedQuadPlus 4 K)) :
    (∃ Y ∈ statedPointFamily (coe_quadPlus 4 K), QuotientGroup.mk' _ g ∈ Y) ↔
      ∃ W, IsSingularPoint W ∧ statedDerivedSubspaceAction (StatedQuadPlus 4 K) g W = W := by
  constructor
  · rintro ⟨Y, hY, hgY⟩
    obtain ⟨W, hW, rfl⟩ := (mem_statedPointFamily_iff Y).1 hY
    exact ⟨W, hW, hgY⟩
  · rintro ⟨W, hW, hgW⟩
    exact ⟨_, (mem_statedPointFamily_iff _).2 ⟨W, hW, rfl⟩, hgW⟩

theorem exists_mem_solidFamilies_iff [Finite K] (g : StatedOmega (StatedQuadPlus 4 K)) :
    (∃ Y, (Y ∈ conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (flag 4 K 4)) ∨
        Y ∈ conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
          (Xstar 4 K (by norm_num)))) ∧ QuotientGroup.mk' _ g ∈ Y) ↔
      ∃ W ∈ singularSubspaces (quadPlus 4 K) 4,
        statedDerivedSubspaceAction (StatedQuadPlus 4 K) g W = W := by
  constructor
  · rintro ⟨Y, hY, hgY⟩
    obtain ⟨W, hW, rfl⟩ := (mem_solidFamilies_iff Y).1 hY
    exact ⟨W, hW, hgY⟩
  · rintro ⟨W, hW, hgW⟩
    exact ⟨_, (mem_solidFamilies_iff _).2 ⟨W, hW, rfl⟩, hgW⟩

theorem map_fixedObjectsStabilizer_eq_iInf (hK : Nat.card K = 2)
    (g : StatedOmega (StatedQuadPlus 4 K))
    (𝓕 : Set (Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))))
    (h𝓕 : ∀ Y, Y ∈ 𝓕 ↔ ∃ W, (IsSingularPoint W ∨ W ∈ singularSubspaces (quadPlus 4 K) 4) ∧
      Y = statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W) :
    (fixedObjectsStabilizer g).map (omegaProjEquiv hK).toMonoidHom =
      ⨅ Y ∈ {Y | Y ∈ 𝓕 ∧ QuotientGroup.mk' _ g ∈ Y}, Y := by
  ext z
  obtain ⟨w, rfl⟩ := (omegaProjEquiv hK).surjective z
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, fixedObjectsStabilizer]
  simp only [Subgroup.mem_iInf, Set.mem_ofPred_eq]
  constructor
  · rintro hw Y ⟨hY, hgY⟩
    obtain ⟨W, hW, rfl⟩ := (h𝓕 Y).1 hY
    exact hw W ⟨hW, hgY⟩
  · rintro hw W ⟨hW, hgW⟩
    exact hw _ ⟨(h𝓕 _).2 ⟨W, hW, rfl⟩, hgW⟩

end CFSG.AGLEmbedding.TrialityTwo
