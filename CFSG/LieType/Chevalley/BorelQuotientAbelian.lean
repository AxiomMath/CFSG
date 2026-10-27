module

public import CFSG.LieType.Chevalley.ChevalleySplitBN

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isMulCommutative_borelSub_quotient_pCore :
    IsMulCommutative (↥(borelSub τ K) ⧸ CFSG.pCore 2 ↥(borelSub τ K)) := by
  let B := borelSub τ K
  let U := posUnipotentSub τ K
  let H := torusSub τ K
  have hUle : U ≤ B := posUnipotentSub_le_borelSub
  have hHle : H ≤ B :=
    Subgroup.subgroupOf_mono _ (le_sup_left : torusGroup τ K ≤ borelGroup τ K)
  have hU2 : IsPGroup 2 U :=
    (((positive_root_triangularity.{0, 0} τ).2 K 2).2.1).of_equiv
      (Subgroup.subgroupOfEquivOfLe posUnipotent_le_adjointGroup).symm
  haveI hUn : (U.subgroupOf B).Normal := normal_posUnipotentSub
  have hTcomm : ∀ g ∈ torusGroup τ K, ∀ g' ∈ torusGroup τ K, g * g' = g' * g :=
    (triangular_borel_structure.{0, 0} τ K).1
  haveI hT : IsMulCommutative (torusGroup τ K) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hTcomm a a.2 b b.2)
  haveI hHcomm : IsMulCommutative H := inferInstance
  have hsup : U.subgroupOf B ⊔ H.subgroupOf B = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUle hHle]
    rw [show U ⊔ H = B from posUnipotentSub_sup_torusSub, Subgroup.subgroupOf_self]
  have hcomm : _root_.commutator ↥B ≤ U.subgroupOf B :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
      (inferInstance : IsMulCommutative (H.subgroupOf B))
  have hU2' : IsPGroup 2 (U.subgroupOf B) :=
    hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUle).symm
  have hUcore : U.subgroupOf B ≤ CFSG.pCore 2 ↥B :=
    le_sSup ⟨inferInstance, hU2'⟩
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (hcomm.trans hUcore)

end CFSG.LieType.Chevalley
