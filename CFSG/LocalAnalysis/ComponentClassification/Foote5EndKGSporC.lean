module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGEven

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven)

theorem endKnownGroupsInputOn_Ly
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Ly) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ hX z K D hK hKs hKt hD hDd hD8 => ?_
  obtain ⟨e⟩ := hX
  refine false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree Sporadic.LySchreier.sporadicOddCoreFree_Ly
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1) ?_
  obtain ⟨hq, -, ⟨eA⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ z hK.1
  have hcard : Nat.card (centralizer ({z} : Set X) ⧸ center (centralizer ({z} : Set X))) =
      19958400 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  refine (RestrictedStd.Spor.compsSatisfy_of_isQuasisimple hq
    (RestrictedStd.Spor.isoInvariant_card_quotient_center {19958400}) hcard).mono
      fun Y _ h => RestrictedStd.Spor.not_small_of_card_quotient ?_
  rw [Set.mem_singleton_iff.1 h]
  exact RestrictedStd.Spor.not_isSmallOrder_A11

theorem endKnownGroupsInputOn_Th
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Th) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ hX z K D hK hKs hKt hD hDd hD8 => ?_
  obtain ⟨e⟩ := hX
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree Sporadic.ThSchreier.sporadicOddCoreFree_Th
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    (RestrictedStd.Spor.compsSatisfy_of_charP
      ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 X
        ⟨e⟩).1 z hK.1).1 _)

theorem endKnownGroupsInputOn_Fi22
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Fi22) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ hX z K D hK hKs hKt hD hDd hD8 => ?_
  obtain ⟨e⟩ := hX
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Fi22
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    fun B hB => RestrictedStd.Spor.not_small_of_card_quotient (by
      rw [Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order e z
        hK.1 B hB]
      exact RestrictedStd.Spor.not_isSmallOrder_U62)

theorem endKnownGroupsInputOn_Fi23
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Fi23) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ hX z K D hK hKs hKt hD hDd hD8 => ?_
  obtain ⟨e⟩ := hX
  refine false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Fi23
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    ((RestrictedStd.Spor.fi23_inner_comps e z hK.1).mono fun Y _ h =>
      RestrictedStd.Spor.not_small_of_card_quotient ?_)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> rw [h]
  · exact RestrictedStd.Spor.not_isSmallOrder_Fi22
  · exact RestrictedStd.Spor.not_isSmallOrder_U62

theorem endKnownGroupsInputOn_Fi24Prime
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Fi24Prime) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ hX z K D hK hKs hKt hD hDd hD8 => ?_
  obtain ⟨e⟩ := hX
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Fi24Prime
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    fun B hB => RestrictedStd.Spor.not_small_of_card_quotient (by
      rw [(CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e z hK.1 B
        hB).1]
      exact RestrictedStd.Spor.not_isSmallOrder_Fi22)

theorem endKnownGroupsInputOn_HN
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .HN) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ hX z K D hK hKs hKt hD hDd hD8 => ?_
  obtain ⟨e⟩ := hX
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree Sporadic.HNOddCore.sporadicOddCoreFree_HN
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    fun B hB => RestrictedStd.Spor.not_small_of_card_quotient (by
      rw [RestrictedStd.Spor.hnLocalComponentsInput_holds X e z hK.1 B hB]
      exact RestrictedStd.Spor.not_isSmallOrder_HS)

end CFSG.ComponentClassification.Foote5
