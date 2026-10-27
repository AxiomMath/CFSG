module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ConnectedJoint

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {k : Type} [Field k]

theorem isPointClosed_torusGroup [IsAlgClosed k] :
    IsPointClosed k (transportPoints (modGLPoint τ k)
      (torusGroup τ k : Set (ModGL τ k))) := by
  have h := (CFSG.StandardType.F4ExplicitPos.ConnectedJoint.isConnectedAlgebraicSubgroup_torus_sup_rootSpan_no117
    (τ := τ) (k := k) ∅).isPointClosed
  have hr : rootSpan τ k ∅ = ⊥ := by
    simp only [rootSpan, Set.mem_empty_iff_false, iSup_false, iSup_bot]
  rw [hr, sup_bot_eq, subgroupPoints_map] at h
  exact h

end CFSG.LieType.AlgebraicGroups
