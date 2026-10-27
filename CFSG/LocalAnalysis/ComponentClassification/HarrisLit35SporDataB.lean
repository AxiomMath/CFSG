module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporData
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.Schreier.J4SNoComp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuterHN
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.HNOddCore.HN

public section

namespace CFSG.ComponentClassification.HarrisLit

section

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification

theorem sporCompData_Co1 :
    SporCompData .Co1 := by
  have hodd := CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Co1
  have hin : Co1LocalComponentsInput := co1LocalComponentsInput_holds
  refine ⟨hodd, (fun G _ _ _ _ ⟨e⟩ t ht B hB => ?_),
    (outer_of_forall_inner fun α => ?_)⟩
  · refine not_small_of_card_quotient ?_
    rw [(hin G e t ht B hB).1]
    exact not_isSmallOrder_G24
  · obtain ⟨g, hg⟩ := Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner α
    exact ⟨g, hg.symm⟩

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification

theorem sporCompData_Fi22 :
    SporCompData .Fi22 := by
  have hodd := CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Fi22
  have hout : Fi22OuterComponentsInput := Sporadic.FischerOddCore.fi22OuterComponentsInput_holds
  refine ⟨hodd, (fun G _ _ _ _ ⟨e⟩ t ht B hB => ?_),
    (fun G _ _ _ _ hG α hα2 hα B hB => ?_)⟩
  · refine not_small_of_card_quotient ?_
    rw [CTI_Fi22_involution_local_components_unitary_quotient_order e t ht B hB]
    exact not_isSmallOrder_U62
  · refine not_small_of_card_quotient ?_
    rcases hout G hG α hα2 hα B hB with h | h <;> rw [h]
    · exact not_isSmallOrder_O8plus2
    · exact not_isSmallOrder_Sp62

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification

theorem sporCompData_Fi24Prime :
    SporCompData .Fi24Prime := by
  have hodd := CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Fi24Prime
  have hout : Fi24primeOuterComponentsInput :=
    Sporadic.FischerOddCore.fi24primeOuterComponentsInput_holds
  refine ⟨hodd, (fun G _ _ _ _ ⟨e⟩ t ht B hB => ?_),
    (fun G _ _ _ _ hG α hα2 hα B hB => ?_)⟩
  · refine not_small_of_card_quotient ?_
    rw [(CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht B
      hB).1]
    exact not_isSmallOrder_Fi22
  · refine not_small_of_card_quotient ?_
    rcases hout G hG α hα2 hα B hB with h | h <;> rw [h]
    · exact not_isSmallOrder_Fi23
    · exact not_isSmallOrder_U62

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.LySchreier
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification

theorem sporCompData_Ly :
    SporCompData .Ly := by
  have hodd := CFSG.Sporadic.LySchreier.sporadicOddCoreFree_Ly
  have hout : LyOuterTrivialInput := lyOuterTrivialInput
  refine ⟨hodd, (fun G _ _ _ _ hG t ht => ?_),
    (outer_of_forall_inner fun α => by
      show α ∈ inner NativeSporadic.Ly
      rw [hout]
      trivial)⟩
  obtain ⟨hq, -, ⟨eA⟩⟩ := involution_centralizers_quasisimple hG t ht
  have hcard : Nat.card (centralizer ({t} : Set G) ⧸ center (centralizer ({t} : Set G))) =
      19958400 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  refine (compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center {19958400})
    hcard).mono fun Y _ h => not_small_of_card_quotient ?_
  rw [Set.mem_singleton_iff.1 h]
  exact not_isSmallOrder_A11

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification

theorem sporCompData_J4 :
    SporCompData .J4 := by
  have hodd := CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_J4
  have hin : J4NoComponentsInput := j4NoComponentsInput
  refine ⟨hodd, (fun G _ _ _ _ hG t ht B hB => absurd hB (hin G hG t ht B)),
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => ?_)⟩
  exfalso
  have eJ : G ≃* Sporadic.J4.J := e.trans (Sporadic.J4.seedEquiv Sporadic.J4.j4Facts.mat)
  have hcard : Nat.card (Outer G) = Nat.card (Outer Sporadic.J4.J) := by
    have h := @Sporadic.J4Schreier.card_outer_congr G Sporadic.J4.J _
      (Subgroup.toGroup Sporadic.J4.J) eJ
    exact h
  have hodd : Odd (Nat.card (Outer G)) := by
    rw [hcard]
    exact Sporadic.J4Schreier.CTU_J4_outer_automorphism_group_odd_order
  exact hα (mem_inner_of_odd_card_outer hodd hα2)

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification

theorem sporCompData_HN :
    SporCompData .HN := by
  have hodd := CFSG.Sporadic.HNOddCore.sporadicOddCoreFree_HN
  have hin : HNLocalComponentsInput := hnLocalComponentsInput_holds
  have hout : FourExactOuterInput := fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB
    CatLeafProof.monsterInnerInput
  refine ⟨hodd, (fun G _ _ _ _ ⟨e⟩ t ht B hB => ?_),
    (fun G _ _ hs hnab hG α hα2 hα => ?_)⟩
  · refine not_small_of_card_quotient ?_
    rw [hin G e t ht B hB]
    exact not_isSmallOrder_HS
  · obtain ⟨-, -, -, -, ⟨eS⟩, -⟩ :=
      hout G hs hnab (Or.inr (Or.inl hG)) α (orderOf_eq_two_of_mul_self hα2 hα) hα
    refine CompsSatisfy.of_mulEquiv isoInvariant_not_small eS ?_
    refine compsSatisfy_perm_ten.mono fun Y _ h => not_small_of_card_quotient ?_
    rw [Set.mem_singleton_iff.1 h]
    exact not_isSmallOrder_A10

end

end CFSG.ComponentClassification.HarrisLit
