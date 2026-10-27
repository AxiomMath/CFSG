module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionStated
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CatalogueBOrthogonalPointAction
open scoped Pointwise

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
variable (Q0 : (ι → K) → K)

@[expose] def statedDerivedLinearHom :
    StatedOmega Q0 →* ((ι → K) ≃ₗ[K] (ι → K)) :=
  (toLinEquiv ι K).toMonoidHom.comp (StatedOmega Q0).subtype

@[expose] def statedDerivedSubspaceAction :
    StatedOmega Q0 →* Equiv.Perm (Submodule K (ι → K)) :=
  (MulAction.toPermHom ((ι → K) ≃ₗ[K] (ι → K)) (Submodule K (ι → K))).comp
    (statedDerivedLinearHom Q0)

theorem statedDerivedSubspaceAction_apply (g : StatedOmega Q0) (W : Submodule K (ι → K)) :
    statedDerivedSubspaceAction Q0 g W = W.map (toLinEquiv ι K g.val).toLinearMap := rfl

private theorem scalar_linear_apply (c : Kˣ) (v : ι → K) :
    toLinEquiv ι K (GeneralLinearGroup.scalar ι c) v = (c : K) • v := by
  rw [toLinEquiv_apply, GeneralLinearGroup.coe_scalar]
  funext i
  exact Matrix.mulVec_diagonal (fun _ => (c : K)) v i

theorem statedScalars_le_subspaceKernel :
    (StatedScalars ι K).subgroupOf (StatedOmega Q0) ≤
      (statedDerivedSubspaceAction Q0).ker := by
  rintro g ⟨c, hc⟩
  change GeneralLinearGroup.scalar ι c = g.val at hc
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro W
  rw [statedDerivedSubspaceAction_apply, ← hc]
  apply le_antisymm
  · rintro v ⟨w, hw, rfl⟩
    rw [LinearEquiv.coe_coe, scalar_linear_apply]
    exact W.smul_mem _ hw
  · intro w hw
    refine ⟨(↑(c⁻¹) : K) • w, W.smul_mem _ hw, ?_⟩
    rw [LinearEquiv.coe_coe, scalar_linear_apply, smul_smul]
    simp

@[expose] def statedProjectiveSubspaceAction :
    StatedProj (StatedOmega Q0) →* Equiv.Perm (Submodule K (ι → K)) :=
  QuotientGroup.lift _ (statedDerivedSubspaceAction Q0) (statedScalars_le_subspaceKernel Q0)

theorem statedProjectiveSubspaceAction_mk (g : StatedOmega Q0) :
    statedProjectiveSubspaceAction Q0 (QuotientGroup.mk' _ g) =
      statedDerivedSubspaceAction Q0 g := rfl

theorem statedProjectiveSubspaceAction_mk_apply
    (g : StatedOmega Q0) (W : Submodule K (ι → K)) :
    statedProjectiveSubspaceAction Q0 (QuotientGroup.mk' _ g) W =
      W.map (toLinEquiv ι K g.val).toLinearMap := rfl

@[expose] def statedDerivedSubspaceStabilizer (W : Submodule K (ι → K)) :
    Subgroup (StatedOmega Q0) :=
  (MulAction.stabilizer ((ι → K) ≃ₗ[K] (ι → K)) W).comap (statedDerivedLinearHom Q0)

theorem mem_statedDerivedSubspaceStabilizer (W : Submodule K (ι → K)) (g : StatedOmega Q0) :
    g ∈ statedDerivedSubspaceStabilizer Q0 W ↔
      W.map (toLinEquiv ι K g.val).toLinearMap = W := Iff.rfl

@[expose] def statedProjectiveSubspaceStabilizer (W : Submodule K (ι → K)) :
    Subgroup (StatedProj (StatedOmega Q0)) :=
  (MulAction.stabilizer (Equiv.Perm (Submodule K (ι → K))) W).comap
    (statedProjectiveSubspaceAction Q0)

theorem mem_statedProjectiveSubspaceStabilizer_mk
    (W : Submodule K (ι → K)) (g : StatedOmega Q0) :
    QuotientGroup.mk' _ g ∈ statedProjectiveSubspaceStabilizer Q0 W ↔
      g ∈ statedDerivedSubspaceStabilizer Q0 W := Iff.rfl

theorem statedDerivedSubspaceStabilizer_map (W : Submodule K (ι → K)) :
    (statedDerivedSubspaceStabilizer Q0 W).map (QuotientGroup.mk' _) =
      statedProjectiveSubspaceStabilizer Q0 W := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_statedProjectiveSubspaceStabilizer_mk Q0 W g).mpr hg
  · intro hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨g, (mem_statedProjectiveSubspaceStabilizer_mk Q0 W g).mp hx, rfl⟩

@[expose] def statedDerivedFlagStabilizer {k : ℕ} (F : Fin k → Submodule K (ι → K)) :
    Subgroup (StatedOmega Q0) := ⨅ i, statedDerivedSubspaceStabilizer Q0 (F i)

@[expose] def statedProjectiveFlagStabilizer {k : ℕ} (F : Fin k → Submodule K (ι → K)) :
    Subgroup (StatedProj (StatedOmega Q0)) := ⨅ i, statedProjectiveSubspaceStabilizer Q0 (F i)

theorem statedDerivedFlagStabilizer_map {k : ℕ} (F : Fin k → Submodule K (ι → K)) :
    (statedDerivedFlagStabilizer Q0 F).map (QuotientGroup.mk' _) =
      statedProjectiveFlagStabilizer Q0 F := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    change g ∈ statedDerivedFlagStabilizer Q0 F at hg
    apply Subgroup.mem_iInf.mpr
    intro i
    exact (mem_statedProjectiveSubspaceStabilizer_mk Q0 (F i) g).mpr
      (Subgroup.mem_iInf.mp hg i)
  · intro hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    refine ⟨g, ?_, rfl⟩
    change QuotientGroup.mk' _ g ∈ statedProjectiveFlagStabilizer Q0 F at hx
    change g ∈ statedDerivedFlagStabilizer Q0 F
    apply Subgroup.mem_iInf.mpr
    intro i
    exact (mem_statedProjectiveSubspaceStabilizer_mk Q0 (F i) g).mp
      (Subgroup.mem_iInf.mp hx i)

variable {Q0} {Q : QuadraticForm K (ι → K)} (hQ : ⇑Q = Q0)
variable (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
    TauCeti.QuadraticMap.orthogonalGroup Q⁆ = elementaryGroup Q)

theorem statedDerivedSubspaceStabilizer_map_elementary (W : Submodule K (ι → K)) :
    (statedDerivedSubspaceStabilizer Q0 W).map (statedOmegaEquiv hQ hE).toMonoidHom =
      MulAction.stabilizer (elementaryGroup Q) W := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change W.map (statedOmegaEquiv hQ hE g).val.toLinearMap = W
    rw [coe_statedOmegaEquiv]
    exact (mem_statedDerivedSubspaceStabilizer Q0 W g).mp hg
  · intro hx
    refine ⟨(statedOmegaEquiv hQ hE).symm x, ?_,
      (statedOmegaEquiv hQ hE).apply_symm_apply x⟩
    change (statedOmegaEquiv hQ hE).symm x ∈ statedDerivedSubspaceStabilizer Q0 W
    rw [mem_statedDerivedSubspaceStabilizer]
    have hv := coe_statedOmegaEquiv hQ hE ((statedOmegaEquiv hQ hE).symm x)
    rw [MulEquiv.apply_symm_apply] at hv
    rw [← hv]
    exact MulAction.mem_stabilizer_iff.mp hx

theorem statedActionEquiv_projection :
    (statedActionEquiv hQ hE).toMonoidHom.comp (QuotientGroup.mk' _) =
      (QuotientGroup.mk' (scalarKernel Q)).comp (statedOmegaEquiv hQ hE).toMonoidHom := by
  ext g
  exact statedActionEquiv_mk hQ hE g

theorem statedProjectiveSubspaceStabilizer_map_elementary (W : Submodule K (ι → K)) :
    (statedProjectiveSubspaceStabilizer Q0 W).map (statedActionEquiv hQ hE).toMonoidHom =
      (MulAction.stabilizer (elementaryGroup Q) W).map (QuotientGroup.mk' (scalarKernel Q)) := by
  rw [← statedDerivedSubspaceStabilizer_map, Subgroup.map_map, statedActionEquiv_projection,
    ← Subgroup.map_map, statedDerivedSubspaceStabilizer_map_elementary]

theorem statedDerivedFlagStabilizer_map_elementary {k : ℕ}
    (F : Fin k → Submodule K (ι → K)) :
    (statedDerivedFlagStabilizer Q0 F).map (statedOmegaEquiv hQ hE).toMonoidHom =
      MulAction.stabilizer (elementaryGroup Q) F := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    apply funext
    intro i
    have hgi := Subgroup.mem_iInf.mp hg i
    have hmem : statedOmegaEquiv hQ hE g ∈ MulAction.stabilizer (elementaryGroup Q) (F i) := by
      rw [← statedDerivedSubspaceStabilizer_map_elementary hQ hE]
      exact ⟨g, hgi, rfl⟩
    exact MulAction.mem_stabilizer_iff.mp hmem
  · intro hx
    refine ⟨(statedOmegaEquiv hQ hE).symm x, ?_,
      (statedOmegaEquiv hQ hE).apply_symm_apply x⟩
    apply Subgroup.mem_iInf.mpr
    intro i
    have hxi : x ∈ MulAction.stabilizer (elementaryGroup Q) (F i) :=
      MulAction.mem_stabilizer_iff.mpr (congrFun (MulAction.mem_stabilizer_iff.mp hx) i)
    rw [← statedDerivedSubspaceStabilizer_map_elementary hQ hE] at hxi
    obtain ⟨g, hg, hgx⟩ := hxi
    have heq : (statedOmegaEquiv hQ hE).symm x = g := by
      rw [← hgx]
      exact (statedOmegaEquiv hQ hE).symm_apply_apply g
    exact heq.symm ▸ hg

theorem statedProjectiveFlagStabilizer_map_elementary {k : ℕ}
    (F : Fin k → Submodule K (ι → K)) :
    (statedProjectiveFlagStabilizer Q0 F).map (statedActionEquiv hQ hE).toMonoidHom =
      (MulAction.stabilizer (elementaryGroup Q) F).map (QuotientGroup.mk' (scalarKernel Q)) := by
  rw [← statedDerivedFlagStabilizer_map, Subgroup.map_map, statedActionEquiv_projection,
    ← Subgroup.map_map, statedDerivedFlagStabilizer_map_elementary]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
