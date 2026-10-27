module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4FamDefs
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.ComponentClassification.CatalogueBStabilizerFamily
open CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise

variable {K : Type} [Field K]

@[expose] def natPerm :
    orthElementaryGroup (quadPlus 4 K) →* Equiv.Perm (Fin 4 ⊕ Fin 4 → K) where
  toFun g := (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).toEquiv
  map_one' := Equiv.ext fun _ => rfl
  map_mul' _ _ := Equiv.ext fun _ => rfl

private def natPermE (K : Type) [Field K] :
    elementaryGroup (quadPlus 4 K) →* Equiv.Perm (Fin 4 ⊕ Fin 4 → K) where
  toFun g := (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).toEquiv
  map_one' := Equiv.ext fun _ => rfl
  map_mul' _ _ := Equiv.ext fun _ => rfl

section Generic

variable {K : Type} [Field K] {H V : Type*} [Group H]

private lemma image_coe_eq_iff_map_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {g : V ≃ₗ[K] V} {W : Submodule K V} :
    (⇑g) '' (W : Set V) = (W : Set V) ↔ W.map (g : V →ₗ[K] V) = W := by
  constructor
  · intro h
    apply SetLike.coe_injective
    rwa [Submodule.map_coe]
  · intro h
    have := congrArg (fun S : Submodule K V => (S : Set V)) h
    simpa [Submodule.map_coe] using this

private lemma fixSet_map_conj (σ : H →* Equiv.Perm V) (g : H) (T : Subgroup H) :
    fixSet σ (T.map (MulAut.conj g).toMonoidHom) = σ g '' fixSet σ T := by
  ext v
  simp only [fixSet, Set.mem_ofPred_eq, Set.mem_image, Subgroup.mem_map]
  constructor
  · intro hv
    refine ⟨(σ g)⁻¹ v, ?_, by simp⟩
    intro t ht
    have hmem := hv (g * t * g⁻¹) ⟨t, ht, rfl⟩
    have h1 : σ g (σ t ((σ g)⁻¹ v)) = v := by
      simpa [MulAut.conj_apply] using hmem
    have h2 : σ g (σ t ((σ g)⁻¹ v)) = σ g ((σ g)⁻¹ v) := by
      rw [h1]
      simp
    exact (σ g).injective h2
  · rintro ⟨w, hw, rfl⟩ t' ⟨t, ht, rfl⟩
    change σ (MulAut.conj g t) (σ g w) = σ g w
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    simp [hw t ht]

private lemma setStab_image_conj (σ : H →* Equiv.Perm V) (g : H) (C : Set V) :
    setStab σ (σ g '' C) = (setStab σ C).map (MulAut.conj g).toMonoidHom := by
  let rho : H →* Equiv.Perm (Set V) := (MulAction.toPermHom (Equiv.Perm V) (Set V)).comp σ
  have h := pointStabilizer_conj rho g C
  change pointStabilizer rho (rho g C) = (pointStabilizer rho C).map
    (MulAut.conj g).toMonoidHom
  exact h.symm

end Generic


private lemma setStab_flag_eq_subgroupOf :
    setStab (natPermE K) (flag 4 K 1 : Set (Fin 4 ⊕ Fin 4 → K)) =
      (MulAction.stabilizer ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
        (flag 4 K 1)).subgroupOf (elementaryGroup (quadPlus 4 K)) := by
  ext g
  rw [setStab, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    rw [Submodule.pointwise_smul_def]
    exact image_coe_eq_iff_map_eq.mp h
  · intro h
    rw [Submodule.pointwise_smul_def] at h
    exact image_coe_eq_iff_map_eq.mpr h

private lemma pointStabilizer_firstPoint_eq_subgroupOf :
    pointStabilizer (elementaryPointAction (quadPlus 4 K))
        (firstPoint (n := 4) (K := K) (by norm_num)) =
      (MulAction.stabilizer ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
        (flag 4 K 1)).subgroupOf (elementaryGroup (quadPlus 4 K)) := by
  ext g
  rw [mem_pointStabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff,
    Submodule.pointwise_smul_def]
  constructor
  · intro h
    have hv : ((elementaryPointAction (quadPlus 4 K)) g
        (firstPoint (n := 4) (K := K) (by norm_num))).val =
        (firstPoint (n := 4) (K := K) (by norm_num)).val := congrArg Subtype.val h
    rw [show (elementaryPointAction (quadPlus 4 K)) g
        (firstPoint (n := 4) (K := K) (by norm_num)) =
        g • firstPoint (n := 4) (K := K) (by norm_num) from rfl,
      elementary_smul_submodule] at hv
    exact hv
  · intro h
    apply Subtype.ext
    rw [show (elementaryPointAction (quadPlus 4 K)) g
        (firstPoint (n := 4) (K := K) (by norm_num)) =
        g • firstPoint (n := 4) (K := K) (by norm_num) from rfl,
      elementary_smul_submodule]
    exact h

private lemma setStab_flag_eq_pointStabilizer :
    setStab (natPermE K) (flag 4 K 1 : Set (Fin 4 ⊕ Fin 4 → K)) =
      pointStabilizer (elementaryPointAction (quadPlus 4 K))
        (firstPoint (n := 4) (K := K) (by norm_num)) := by
  rw [setStab_flag_eq_subgroupOf, pointStabilizer_firstPoint_eq_subgroupOf]


private lemma fixSet_coe_eq_flag [CharP K 2] (U0 : Sylow 2 (elementaryGroup (quadPlus 4 K)))
    (hU0 : (U0 : Subgroup (elementaryGroup (quadPlus 4 K))) =
      (posUnip 4 K).subgroupOf (elementaryGroup (quadPlus 4 K))) :
    fixSet (natPermE K) (U0 : Subgroup (elementaryGroup (quadPlus 4 K))) =
      (flag 4 K 1 : Set (Fin 4 ⊕ Fin 4 → K)) := by
  ext v
  rw [fixSet, Set.mem_ofPred_eq, hU0,
    ← (orthogonal_geometry_split_unipotent_invariant_singular_subspaces
      (r := 4) (K := K) (by norm_num)).1]
  constructor
  · intro h g hg
    exact h ⟨g, posUnip_le_orthElementaryGroup hg⟩ (Subgroup.mem_subgroupOf.2 hg)
  · intro h t ht
    exact h (t : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
      (Subgroup.mem_subgroupOf.1 ht)

private lemma setStab_fixSet_smul_sylow [CharP K 2] (U0 : Sylow 2 (elementaryGroup (quadPlus 4 K)))
    (hU0 : (U0 : Subgroup (elementaryGroup (quadPlus 4 K))) =
      (posUnip 4 K).subgroupOf (elementaryGroup (quadPlus 4 K)))
    (g : elementaryGroup (quadPlus 4 K)) :
    setStab (natPermE K) (Set.univ ∩ fixSet (natPermE K)
        ((g • U0 : Sylow 2 (elementaryGroup (quadPlus 4 K))) :
          Subgroup (elementaryGroup (quadPlus 4 K)))) =
      (pointStabilizer (elementaryPointAction (quadPlus 4 K))
        (firstPoint (n := 4) (K := K) (by norm_num))).map (MulAut.conj g).toMonoidHom := by
  have hcoe : ((g • U0 : Sylow 2 (elementaryGroup (quadPlus 4 K))) :
      Subgroup (elementaryGroup (quadPlus 4 K))) =
      (U0 : Subgroup (elementaryGroup (quadPlus 4 K))).map
        (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    congr 1
  have hUfix : fixSet (natPermE K) (U0 : Subgroup (elementaryGroup (quadPlus 4 K))) =
      (flag 4 K 1 : Set (Fin 4 ⊕ Fin 4 → K)) := fixSet_coe_eq_flag U0 hU0
  rw [Set.univ_inter, hcoe, fixSet_map_conj, setStab_image_conj, hUfix,
    setStab_flag_eq_pointStabilizer (K := K)]

private lemma sylowFamilyOn_natPermE_eq_conjugacyFamily [Finite K] [CharP K 2] :
    sylowFamilyOn (natPermE K) Set.univ =
      conjugacyFamily (pointStabilizer (elementaryPointAction (quadPlus 4 K))
        (firstPoint (n := 4) (K := K) (by norm_num))) := by
  obtain ⟨U0, hU0⟩ := posUnip_isSylow (r := 4) (K := K) 2 (by norm_num)
    (fun a ha => map_flag_top_ne_Xstar (K := K) (by norm_num) ha)
  let U0' : Sylow 2 (elementaryGroup (quadPlus 4 K)) := U0
  have hU0' : (U0' : Subgroup (elementaryGroup (quadPlus 4 K))) =
      (posUnip 4 K).subgroupOf (elementaryGroup (quadPlus 4 K)) := hU0
  let : Finite (elementaryGroup (quadPlus 4 K)) := finite_orthElementaryGroup
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction.IsPretransitive (elementaryGroup (quadPlus 4 K))
      (Sylow 2 (elementaryGroup (quadPlus 4 K))) := Sylow.isPretransitive_of_finite
  ext U
  constructor
  · rintro ⟨T, rfl⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (elementaryGroup (quadPlus 4 K)) U0' T
    refine ⟨g, ?_⟩
    rw [← hg]
    exact (setStab_fixSet_smul_sylow U0' hU0' g).symm
  · rintro ⟨g, rfl⟩
    exact ⟨g • U0', setStab_fixSet_smul_sylow U0' hU0' g⟩


private lemma elemScalars_eq_bot {r : ℕ} [CharP K 2] (hr : 1 ≤ r) :
    elemScalars r K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' : (x : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈ scalars K _ := by
    rw [elemScalars] at hx
    exact Subgroup.mem_subgroupOf.1 hx
  exact Subtype.ext (eq_one_of_mem_orthogonalGroup_scalars hr
    (elementaryGroup_le_orthogonalGroup _ x.2) hx')

private lemma scalarKernel_eq_bot [CharP K 2] :
    scalarKernel (quadPlus 4 K) = ⊥ := by
  change elemScalars 4 K = ⊥
  exact elemScalars_eq_bot (K := K) (r := 4) (by norm_num)

private noncomputable def projElementaryEquivPlus [CharP K 2] :
    ProjectiveGroup (quadPlus 4 K) ≃* elementaryGroup (quadPlus 4 K) :=
  QuotientGroup.liftEquiv (N := scalarKernel (quadPlus 4 K))
    (φ := MonoidHom.id (elementaryGroup (quadPlus 4 K)))
    (by exact Function.surjective_id)
    (by rw [MonoidHom.ker_id]; exact scalarKernel_eq_bot (K := K))

private noncomputable def statedProjEquivPlus [CharP K 2] :
    StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃* elementaryGroup (quadPlus 4 K) :=
  (statedActionEquiv (coe_quadPlus 4 K)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
      (n := 4) (K := K) (by norm_num))).trans (projElementaryEquivPlus (K := K))

private lemma projElementaryEquivPlus_mk [CharP K 2] (A : elementaryGroup (quadPlus 4 K)) :
    projElementaryEquivPlus (K := K) (QuotientGroup.mk' (scalarKernel (quadPlus 4 K)) A) = A := by
  unfold projElementaryEquivPlus
  rw [QuotientGroup.mk'_apply, QuotientGroup.liftEquiv_mk]
  rfl

private lemma statedProjEquivPlus_mk [CharP K 2] (A : StatedOmega (StatedQuadPlus 4 K)) :
    statedProjEquivPlus (K := K) (QuotientGroup.mk' _ A) =
      statedOmegaEquiv (coe_quadPlus 4 K)
        (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
          (n := 4) (K := K) (by norm_num)) A := by
  unfold statedProjEquivPlus
  rw [MulEquiv.trans_apply, QuotientGroup.mk'_apply, statedActionEquiv_mk]
  rw [← QuotientGroup.mk'_apply (scalarKernel (quadPlus 4 K))
    (statedOmegaEquiv (coe_quadPlus 4 K)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
        (n := 4) (K := K) (by norm_num)) A)]
  exact projElementaryEquivPlus_mk _

private lemma firstPointStabilizer_map [CharP K 2] :
    (firstPointStabilizer (n := 4) (K := K)).map
        (statedProjEquivPlus (K := K)).toMonoidHom =
      (MulAction.stabilizer ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
        (flag 4 K 1)).subgroupOf (elementaryGroup (quadPlus 4 K)) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ x
    change QuotientGroup.mk' _ A ∈ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
      (flag 4 K 1) at hx
    rw [mem_statedProjectiveSubspaceStabilizer_mk, mem_statedDerivedSubspaceStabilizer] at hx
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Submodule.pointwise_smul_def]
    change Submodule.map (DistribSMul.toLinearMap K (Fin 4 ⊕ Fin 4 → K)
      ↑(statedProjEquivPlus (K := K) (QuotientGroup.mk' _ A))) (flag 4 K 1) = flag 4 K 1
    rw [statedProjEquivPlus_mk (K := K) A]
    change Submodule.map (DistribSMul.toLinearMap K (Fin 4 ⊕ Fin 4 → K)
      (toLinEquiv (Fin 4 ⊕ Fin 4) K A.val)) (flag 4 K 1) = flag 4 K 1
    exact hx
  · intro hg
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff,
      Submodule.pointwise_smul_def] at hg
    refine ⟨QuotientGroup.mk' _ ((statedOmegaEquiv (coe_quadPlus 4 K)
        (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
          (n := 4) (K := K) (by norm_num))).symm g), ?_, ?_⟩
    · change (QuotientGroup.mk' _ ((statedOmegaEquiv (coe_quadPlus 4 K)
        (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
          (n := 4) (K := K) (by norm_num))).symm g)) ∈
        statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 1)
      rw [mem_statedProjectiveSubspaceStabilizer_mk, mem_statedDerivedSubspaceStabilizer]
      have hval : toLinEquiv (Fin 4 ⊕ Fin 4) K
          ((statedOmegaEquiv (coe_quadPlus 4 K)
          (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
            (n := 4) (K := K) (by norm_num))).symm g).val =
          (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := by
        rw [← coe_statedOmegaEquiv (coe_quadPlus 4 K)
          (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
            (n := 4) (K := K) (by norm_num))]
        rw [MulEquiv.apply_symm_apply]
      rw [hval]
      exact hg
    · change statedProjEquivPlus (K := K) (QuotientGroup.mk' _ ((statedOmegaEquiv (coe_quadPlus 4 K)
        (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
          (n := 4) (K := K) (by norm_num))).symm g)) = g
      rw [statedProjEquivPlus_mk (K := K) ((statedOmegaEquiv (coe_quadPlus 4 K)
        (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
          (n := 4) (K := K) (by norm_num))).symm g), MulEquiv.apply_symm_apply]

private lemma pointStabilizer_map_symm [CharP K 2] :
    (pointStabilizer (elementaryPointAction (quadPlus 4 K))
        (firstPoint (n := 4) (K := K) (by norm_num))).map
        (statedProjEquivPlus (K := K)).symm.toMonoidHom =
      firstPointStabilizer (n := 4) (K := K) := by
  have h := firstPointStabilizer_map (K := K)
  have hP : pointStabilizer (elementaryPointAction (quadPlus 4 K))
      (firstPoint (n := 4) (K := K) (by norm_num)) =
      (MulAction.stabilizer ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
        (flag 4 K 1)).subgroupOf (elementaryGroup (quadPlus 4 K)) :=
    pointStabilizer_firstPoint_eq_subgroupOf (K := K)
  calc (pointStabilizer (elementaryPointAction (quadPlus 4 K))
        (firstPoint (n := 4) (K := K) (by norm_num))).map
        (statedProjEquivPlus (K := K)).symm.toMonoidHom
      = ((firstPointStabilizer (n := 4) (K := K)).map
          (statedProjEquivPlus (K := K)).toMonoidHom).map
          (statedProjEquivPlus (K := K)).symm.toMonoidHom := by
        rw [hP, h]
    _ = firstPointStabilizer (n := 4) (K := K) := by
        rw [Subgroup.map_map]
        have hcomp : (statedProjEquivPlus (K := K)).symm.toMonoidHom.comp
            (statedProjEquivPlus (K := K)).toMonoidHom =
            MonoidHom.id (StatedProj (StatedOmega (StatedQuadPlus 4 K))) := by
          ext x
          exact (statedProjEquivPlus (K := K)).symm_apply_apply x
        rw [hcomp, Subgroup.map_id]

private lemma familyTransport_statedProjEquivPlus_symm_sylowFamily [Finite K] [CharP K 2] :
    familyTransport (statedProjEquivPlus (K := K)).symm
        (sylowFamilyOn (natPermE K) Set.univ) =
      statedPointFamily (coe_quadPlus 4 K) := by
  rw [sylowFamilyOn_natPermE_eq_conjugacyFamily]
  rw [familyTransport_conjugacy]
  rw [pointStabilizer_map_symm]
  rw [statedPointFamily_eq_conjugacyFamily (by norm_num)]

private lemma familyTransport_trans {G J L : Type*} [Group G] [Group J] [Group L]
    (e : G ≃* J) (f : J ≃* L) (F : Set (Subgroup G)) :
    familyTransport (e.trans f) F = familyTransport f (familyTransport e F) := by
  ext U
  simp only [familyTransport_apply, Set.mem_image]
  constructor
  · rintro ⟨V, hV, rfl⟩
    exact ⟨V.map e.toMonoidHom, ⟨V, hV, rfl⟩, by
      rw [show (e.trans f).toMonoidHom = f.toMonoidHom.comp e.toMonoidHom from rfl,
        ← Subgroup.map_map]⟩
  · rintro ⟨W, ⟨V, hV, rfl⟩, rfl⟩
    exact ⟨V, hV, by
      rw [show (e.trans f).toMonoidHom = f.toMonoidHom.comp e.toMonoidHom from rfl,
        ← Subgroup.map_map]⟩

theorem exists_familyTransport_sylowFamilyOn_natPerm [Finite K] [CharP K 2] :
    ∃ ν : orthElementaryGroup (quadPlus 4 K) ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K),
      familyTransport ν (sylowFamilyOn natPerm Set.univ) =
        projectivePointFamily (coordinateQuadPlus 4 K) := by
  let e : StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃*
      orthElementaryGroup (quadPlus 4 K) := statedProjEquivPlus (K := K)
  let ν : orthElementaryGroup (quadPlus 4 K) ≃*
      matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    e.symm.trans (plusCoordinateEquiv 4 K)
  refine ⟨ν, ?_⟩
  have hν : ν = e.symm.trans (plusCoordinateEquiv 4 K) := rfl
  rw [hν, familyTransport_trans e.symm (plusCoordinateEquiv 4 K)]
  change familyTransport (plusCoordinateEquiv 4 K)
      (familyTransport (statedProjEquivPlus (K := K)).symm
        (sylowFamilyOn (natPermE K) Set.univ)) =
    projectivePointFamily (coordinateQuadPlus 4 K)
  rw [familyTransport_statedProjEquivPlus_symm_sylowFamily]
  exact plusCoordinate_pointFamily

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
