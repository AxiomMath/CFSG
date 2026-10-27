module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseB
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBMSpor
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGEven

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.Blueprint

theorem endKnownGroupsInputOn_B
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .B) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ hX z K D hK hKs hKt hD hDd hD8 => ?_
  obtain ⟨e⟩ := hX
  refine false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree BMCase.sporadicOddCoreFree_B
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1) fun B hB => ?_
  obtain ⟨-, hiso, -⟩ :=
    Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ z hK.1
      B hB
  refine RestrictedStd.Spor.not_small_of_card_quotient ?_
  rcases hiso with hiso | hiso
  · obtain ⟨φ⟩ := hiso
    rw [Nat.card_congr φ.toEquiv, LieType.Chevalley.C2E6Std.card_stdGroup]
    exact RestrictedStd.Spor.not_isSmallOrder_twoE62
  · obtain ⟨φ⟩ := hiso
    obtain ⟨ψ⟩ := Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
    rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
      Monster.B.E6.FieldInvF4.card_groupJ]
    exact RestrictedStd.Spor.not_isSmallOrder_F42

theorem endKnownGroupsInputOn_M
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .M) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ hX z K D hK hKs hKt hD hDd hD8 => ?_
  obtain ⟨e⟩ := hX
  obtain ⟨eG⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    fun B hB => GSThmB.MonsterArith.not_smallCentralQuotient
      (CatLeafProof.monsterLocalComponentsInput X inferInstance ⟨e⟩ z hK.1 B hB).1 (by
        rw [← YGroups.Y443.natCard_Gmat_eq_monsterOrder, ← Nat.card_congr eG.toEquiv]
        exact (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_subgroup_dvd_card B).trans
          (Subgroup.card_subgroup_dvd_card _)))

end CFSG.ComponentClassification.Foote5
