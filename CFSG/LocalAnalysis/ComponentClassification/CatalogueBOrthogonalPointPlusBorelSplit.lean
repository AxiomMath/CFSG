module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelBasic
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryIndex
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.ClassicalGroups.Orthogonal.Simple

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalPointAction
open scoped Pointwise

variable (n : ℕ) (K : Type) [Field K]

@[expose] def plusDerivedEquiv (hn : 3 ≤ n) :
    StatedOmega (StatedQuadPlus n K) ≃* orthElementaryGroup (quadPlus n K) :=
  statedOmegaEquiv (coe_quadPlus n K)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn)

theorem plusDerivedEquiv_val (hn : 3 ≤ n) (g : StatedOmega (StatedQuadPlus n K)) :
    (plusDerivedEquiv n K hn g).val = toLinEquiv (Fin n ⊕ Fin n) K g.val := rfl

theorem plusDerivedEquiv_scalars (hn : 3 ≤ n) :
    ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))).map
        (plusDerivedEquiv n K hn).toMonoidHom = elemScalars n K :=
  statedActionEquiv_scalarKernel (coe_quadPlus n K)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn)

@[expose] def plusProjectiveEquiv (hn : 3 ≤ n) :
    StatedProj (StatedOmega (StatedQuadPlus n K)) ≃*
      (orthElementaryGroup (quadPlus n K) ⧸ elemScalars n K) :=
  statedActionEquiv (coe_quadPlus n K)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn)

theorem plusProjectiveEquiv_mk (hn : 3 ≤ n) (g : StatedOmega (StatedQuadPlus n K)) :
    plusProjectiveEquiv n K hn (QuotientGroup.mk' _ g) =
      QuotientGroup.mk' (elemScalars n K) (plusDerivedEquiv n K hn g) := rfl

theorem plusProjectiveSubspaceAction (hn : 3 ≤ n)
    (g : StatedProj (StatedOmega (StatedQuadPlus n K))) :
    statedProjectiveSubspaceAction (StatedQuadPlus n K) g =
      splitProjAction n K (plusProjectiveEquiv n K hn g) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [plusProjectiveEquiv_mk]
  apply Equiv.ext
  intro W
  rfl

@[expose] def plusMatrixUnipotent : Subgroup (GL (Fin n ⊕ Fin n) K) :=
  (posUnip n K).comap (toLinEquiv (Fin n ⊕ Fin n) K).toMonoidHom

theorem toMatrix_toLinEquiv (g : GL (Fin n ⊕ Fin n) K) :
    LinearMap.toMatrix' (toLinEquiv (Fin n ⊕ Fin n) K g).toLinearMap = g.val := by
  change LinearMap.toMatrix' (Matrix.toLin' g.val) = g.val
  exact LinearMap.toMatrix'_toLin' g.val

theorem mem_plusMatrixUnipotent (g : GL (Fin n ⊕ Fin n) K) :
    g ∈ plusMatrixUnipotent n K ↔
      ∃ (A : GL (Fin n) K) (C : Matrix (Fin n) (Fin n) K),
        (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular ∧
        (∀ i, (A : Matrix (Fin n) (Fin n) K) i i = 1) ∧
        Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
        g.val = fromBlocks (A : Matrix (Fin n) (Fin n) K)
          ((A : Matrix (Fin n) (Fin n) K) * C) 0
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
  change toLinEquiv (Fin n ⊕ Fin n) K g ∈ posUnip n K ↔ _
  rw [mem_posUnip_iff, toMatrix_toLinEquiv]

theorem plusMatrixUnipotent_le_derived (hn : 3 ≤ n) :
    plusMatrixUnipotent n K ≤ StatedOmega (StatedQuadPlus n K) := by
  rw [statedOmega_eq_comap (coe_quadPlus n K),
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn]
  exact Subgroup.comap_mono posUnip_le_orthElementaryGroup

@[expose] def plusDerivedUnipotent : Subgroup (StatedOmega (StatedQuadPlus n K)) :=
  (plusMatrixUnipotent n K).subgroupOf (StatedOmega (StatedQuadPlus n K))

theorem plusDerivedUnipotent_map (hn : 3 ≤ n) :
    (plusDerivedUnipotent n K).map (plusDerivedEquiv n K hn).toMonoidHom =
      (posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K)) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (plusDerivedEquiv n K hn g).val ∈ posUnip n K
    rw [plusDerivedEquiv_val]
    exact hg
  · intro hx
    refine ⟨(plusDerivedEquiv n K hn).symm x, ?_,
      (plusDerivedEquiv n K hn).apply_symm_apply x⟩
    change toLinEquiv (Fin n ⊕ Fin n) K ((plusDerivedEquiv n K hn).symm x).val ∈ posUnip n K
    rw [← plusDerivedEquiv_val n K hn, MulEquiv.apply_symm_apply]
    exact hx

@[expose] def plusProjectiveUnipotent :
    Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
  (plusDerivedUnipotent n K).map (QuotientGroup.mk' _)

theorem plusProjectiveUnipotent_map (hn : 3 ≤ n) :
    (plusProjectiveUnipotent n K).map (plusProjectiveEquiv n K hn).toMonoidHom =
      ((posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K))).map
        (QuotientGroup.mk' (elemScalars n K)) := by
  rw [plusProjectiveUnipotent, Subgroup.map_map]
  have hp : (plusProjectiveEquiv n K hn).toMonoidHom.comp (QuotientGroup.mk' _) =
      (QuotientGroup.mk' (elemScalars n K)).comp (plusDerivedEquiv n K hn).toMonoidHom := by
    ext g
    exact plusProjectiveEquiv_mk n K hn g
  rw [hp, ← Subgroup.map_map, plusDerivedUnipotent_map]

@[expose] def plusDerivedBorel : Subgroup (StatedOmega (StatedQuadPlus n K)) :=
  statedDerivedFlagStabilizer (StatedQuadPlus n K) (stdFlag n K)

@[expose] def plusProjectiveBorel :
    Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
  statedProjectiveFlagStabilizer (StatedQuadPlus n K) (stdFlag n K)

theorem plusDerivedBorel_map (hn : 3 ≤ n) :
    (plusDerivedBorel n K).map (plusDerivedEquiv n K hn).toMonoidHom =
      (flagStab n K).subgroupOf (orthElementaryGroup (quadPlus n K)) := by
  rw [plusDerivedBorel, ← stabilizer_stdFlag]
  exact statedDerivedFlagStabilizer_map_elementary (coe_quadPlus n K)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn) (stdFlag n K)

theorem plusProjectiveBorel_map (hn : 3 ≤ n) :
    (plusProjectiveBorel n K).map (plusProjectiveEquiv n K hn).toMonoidHom =
      ((flagStab n K).subgroupOf (orthElementaryGroup (quadPlus n K))).map
        (QuotientGroup.mk' (elemScalars n K)) := by
  rw [plusProjectiveBorel, ← stabilizer_stdFlag]
  exact statedProjectiveFlagStabilizer_map_elementary (coe_quadPlus n K)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn) (stdFlag n K)

theorem plusDerivedBorel_project :
    (plusDerivedBorel n K).map (QuotientGroup.mk' _) = plusProjectiveBorel n K :=
  statedDerivedFlagStabilizer_map (StatedQuadPlus n K) (stdFlag n K)

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
