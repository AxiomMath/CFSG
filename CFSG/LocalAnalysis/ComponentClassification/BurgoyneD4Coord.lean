module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Tri
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped Pointwise

variable (K : Type) [Field K] {d : ℕ}

abbrev Qc : QuadraticForm K (Fin (2 * 4) → K) := coordinateQuadPlus 4 K

abbrev Es : StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃*
    StatedProj (matrixDerived (Qc K)) :=
  plusCoordinateEquiv 4 K

abbrev rc : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin (2 * 4) → K) := reindexVectorEquiv (plusIndexEquiv 4)

abbrev cx₁ : Set (Subgroup (StatedProj (matrixDerived (Qc K)))) :=
  familyTransport (Es K)
    (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)))

abbrev cx₂ : Set (Subgroup (StatedProj (matrixDerived (Qc K)))) :=
  familyTransport (Es K)
    (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
      (Xstar 4 K (by omega))))

variable {K}

theorem rc_symm_apply (v : Fin (2 * 4) → K) :
    Qc K v = quadPlus 4 K ((rc K).symm v) := rfl

theorem map_rc_symm (W : Submodule K (Fin (2 * 4) → K)) :
    (W.map (rc K).symm.toLinearMap).map (rc K).toLinearMap = W := by
  rw [← Submodule.map_comp]
  convert Submodule.map_id W
  ext v
  simp

theorem statedStab_map_Es (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W).map (Es K).toMonoidHom =
      subStab (Qc K) (W.map (rc K).toLinearMap) := by
  rw [statedProjectiveSubspaceStabilizer_eq_pointStabilizer]
  refine pointStabilizer_map_equiv _ _ (Es K) (Submodule.orderIsoMapComap (rc K)).toEquiv
    (fun g U => ?_) W
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  change subAction (Qc K) (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K)
    (coe_quadPlus 4 K) (QuotientGroup.mk' _ A)) (U.map (rc K).toLinearMap) =
    (statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (QuotientGroup.mk' _ A) U).map
      (rc K).toLinearMap
  rw [statedProjectiveReindexEquiv_mk, statedProjectiveSubspaceAction_mk_apply]
  change (U.map (rc K).toLinearMap).map (matrixLinearEquiv
    (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
      A).val).toLinearMap = _
  rw [statedDerivedReindexEquiv_val, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro v
  change matrixLinearEquiv (reindexMatrixEquiv (plusIndexEquiv 4) A.val) (rc K v) =
    rc K (toLinEquiv (Fin 4 ⊕ Fin 4) K A.val v)
  rw [reindexMatrixEquiv_mulVec, toLinEquiv_apply]

theorem isTS_map_rc {W : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hW : W ∈ singularSubspaces (quadPlus 4 K) 4) : IsTS (Qc K) 4 (W.map (rc K).toLinearMap) := by
  refine ⟨by rw [LinearEquiv.finrank_map_eq]; exact hW.1, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  change Qc K (rc K v) = 0
  rw [rc_symm_apply, LinearEquiv.symm_apply_apply]
  exact hW.2 v hv

theorem cx_union_eq_tsFam [Finite K] : cx₁ K ∪ cx₂ K = tsFam (Qc K) := by
  obtain ⟨hX, hXs, -, -, hcover, -⟩ :=
    orthogonal_geometry_split_maximal_family_orbits (K := K) (r := 4) (by omega)
  have hmem : ∀ {X₀ : Submodule K (Fin 4 ⊕ Fin 4 → K)},
      X₀ ∈ singularSubspaces (quadPlus 4 K) 4 →
      familyTransport (Es K)
        (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) X₀)) ⊆
        tsFam (Qc K) := by
    intro X₀ hX₀
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    change ((statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) X₀).map
      (MulAut.conj g).toMonoidHom).map (Es K).toMonoidHom ∈ tsFam (Qc K)
    rw [subgroupTransport_conj, statedStab_map_Es, subStab_map_conj]
    exact subStab_mem_tsFam _ ((isTS_map_rc hX₀).subAction _)
  refine Set.Subset.antisymm (Set.union_subset (hmem hX) (hmem hXs)) ?_
  rintro _ ⟨W, hW, rfl⟩
  set Ws := W.map (rc K).symm.toLinearMap with hWs
  have hWs' : Ws ∈ singularSubspaces (quadPlus 4 K) 4 := by
    refine ⟨by rw [hWs, LinearEquiv.finrank_map_eq]; exact hW.1, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hW.2 v hv
  have key : ∀ {X₀ : Submodule K (Fin 4 ⊕ Fin 4 → K)},
      Ws ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K)) X₀ →
      subStab (Qc K) W ∈ familyTransport (Es K)
        (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) X₀)) := by
    intro X₀ hX₀
    obtain ⟨a, ha, haX⟩ := mem_orbit_elementary.1 hX₀
    set g₀ := (plusDerivedEquiv 4 K (by omega)).symm ⟨a, ha⟩ with hg₀
    have hag : toLinEquiv (Fin 4 ⊕ Fin 4) K g₀.val = a := by
      have := congrArg Subtype.val ((plusDerivedEquiv 4 K (by omega)).apply_symm_apply ⟨a, ha⟩)
      rw [← hg₀] at this
      exact this
    refine ⟨_, ⟨QuotientGroup.mk' _ g₀, rfl⟩, ?_⟩
    change ((statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) X₀).map
      (MulAut.conj (QuotientGroup.mk' _ g₀)).toMonoidHom).map (Es K).toMonoidHom = _
    rw [statedProjectiveSubspaceStabilizer_map_conj, statedProjectiveSubspaceAction_mk_apply, hag,
      statedStab_map_Es]
    congr 1
    rw [← map_rc_symm W, ← hWs, ← haX]
    rfl
  rcases hcover Ws hWs' with h | h
  · exact Or.inl (key h)
  · exact Or.inr (key h)

theorem ptFam_coord :
    familyTransport (Es K) (statedPointFamily (coe_quadPlus 4 K)) = ptFam (Qc K) :=
  (plusCoordinate_pointFamily (n := 4) (K := K)).trans (projectivePointFamily_eq_ptFam _)

variable (K) in
abbrev swapc : MulAut (StatedProj (matrixDerived (Qc K))) :=
  MulAut.congr (Es K) (plusSwapAut 4 K (by omega))

theorem swapc_ptFam : swapc K • ptFam (Qc K) = ptFam (Qc K) := by
  rw [← ptFam_coord, ← familyTransport_automorphism, plusSwapAut_smul_statedPointFamily]

theorem swapc_cx₁ : swapc K • cx₁ K = cx₂ K := by
  rw [← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_flag]

theorem swapc_cx₂ : swapc K • cx₂ K = cx₁ K := by
  rw [← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_Xstar]

theorem cx₁_ne_cx₂ [Finite K] : cx₁ K ≠ cx₂ K := fun h =>
  conjugacyFamily_flag_ne_Xstar 4 K (by omega) ((familyTransport (Es K)).injective h)

theorem orbit_ptFam_subset [Finite K] :
    MulAction.orbit (MulAut (StatedProj (matrixDerived (Qc K)))) (ptFam (Qc K)) ⊆
      {ptFam (Qc K), cx₁ K, cx₂ K} := by
  rw [← ptFam_coord, ← familyTransport_orbit]
  rintro _ ⟨T, hT, rfl⟩
  rcases stated_pointFamily_orbit_subset (K := K) (n := 4) rfl hT with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem d4Geom_coord [Finite K] : D4Geom (Qc K) := fun _ hz hzF =>
  ⟨cx₁ K, cx₂ K, cycle_of_odd orbit_ptFam_subset swapc_ptFam swapc_cx₁ swapc_cx₂ cx₁_ne_cx₂ hz hzF,
    cx_union_eq_tsFam⟩

theorem ptRigid_coord : PtRigid (Qc K) := by
  intro L L' h
  have hreg := regular_coordinateQuadPlus 4 K (by omega)
  exact projectivePointStabilizer_injective_native (Qc K)
    (commutator_coordinateQuadPlus 4 K (by omega)) hreg.1 hreg.2
    ((projectivePointStabilizer_eq_subStab _ L).trans
      (h.trans (projectivePointStabilizer_eq_subStab _ L').symm))

theorem congr_conj_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (x : G) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext z
  simp [MulAut.conj_apply]

theorem conj_injective_of_simple {G : Type*} [Group G] [IsSimpleGroup G] [Group.IsPerfect G] :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exfalso
      apply Group.IsPerfect.not_isMulCommutative G
      exact ⟨⟨fun a b => (mem_center_iff.1 (h ▸ mem_top a) b).symm⟩⟩
  intro g g' e
  have hc : g'⁻¹ * g ∈ center G := mem_center_iff.2 fun x => by
    have h1 := congrArg (fun α : MulAut G => α x) e
    simp only [MulAut.conj_apply] at h1
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem conj_injective_of_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : Function.Injective (MulAut.conj : G →* MulAut G)) :
    Function.Injective (MulAut.conj : G' →* MulAut G') := by
  intro x x' hxx'
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨x', rfl⟩ := e.surjective x'
  rw [← congr_conj_equiv, ← congr_conj_equiv] at hxx'
  rw [h ((MulAut.congr e).injective hxx')]

theorem conj_injective_coord :
    Function.Injective (MulAut.conj : StatedProj (matrixDerived (Qc K)) →*
      MulAut (StatedProj (matrixDerived (Qc K)))) := by
  have := isSimpleGroup_statedProj_statedOmega_quadPlus (K := K) (n := 4) (by omega)
  have := isPerfect_statedOmega_quadPlus (K := K) (n := 4) (by omega)
  exact conj_injective_of_equiv (Es K) conj_injective_of_simple

theorem mem_familyAut_iff (Q : QuadraticForm K (Fin d → K))
    (α : MulAut (StatedProj (matrixDerived Q))) :
    α ∈ projectivePointFamilyAut Q ↔ α • ptFam Q = ptFam Q := by
  have h : (projectivePointFamily Q : Set (Subgroup (StatedProj (matrixDerived Q)))) = ptFam Q :=
    projectivePointFamily_eq_ptFam Q
  exact Iff.of_eq (congrArg (fun F : Set (Subgroup (StatedProj (matrixDerived Q))) => α • F = F) h)

end CFSG.ComponentClassification.Burgoyne.D4
