module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporTools
public import CFSG.Monster.B.CTIB.ComponentsSeventeen
public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.YGroups.Y443.Tri.Finiteness

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem singleComponentCleanAt_B :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .B) := by
  refine singleComponentCleanAt_of_primePow 17 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · rw [← card_quot_center_subgroupOf hK.1, pow_one]
    exact (Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen
      hP y hy2 _ (isComponent_subgroupOf_of_isTwoComponentIn hK hq)).2.2
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 17 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.B
    rw [RankThree.OddKernel.card_B_eq]
    norm_num

theorem singleComponentCleanAt_M
    :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .M) := by
  refine singleComponentCleanAt_of_primePow 2 41 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · rw [← card_quot_center_subgroupOf hK.1]
    exact (CatLeafProof.monsterLocalComponentsInput T hT hP y hy2 _
      (isComponent_subgroupOf_of_isTwoComponentIn hK hq)).1
  · obtain ⟨e⟩ := hP
    have := hT
    obtain ⟨E⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
    rw [Nat.card_congr E.toEquiv, YGroups.Y443.natCard_Gmat_eq_monsterOrder]
    norm_num [Open.monsterOrder]

end CFSG.ComponentClassification.Sol76.Sig
