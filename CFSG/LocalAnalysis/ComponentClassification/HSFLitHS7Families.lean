module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7OddLie
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7AltMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpReduce

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem psu_three_three_admissible : StatedLieAdmissible .PSU 3 3 1 := by
  refine ⟨Nat.prime_three, le_rfl, le_rfl, ?_⟩
  decide

theorem false_of_outer_evenLie
    (hF : IsSimpleGroup ↥(generalizedFitting G)) (heven : EvenLieType ↥(generalizedFitting G))
    {t : G} (ht : orderOf t = 2) (htF : t ∉ generalizedFitting G) {L : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (h7 : Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7))) : False := by
  obtain ⟨σ, hσ2, hσout, hP, ⟨e7⟩⟩ := exists_outer_properFixedComponent hF ht htF hLt hL h7
  obtain ⟨τ, n, f, hadm, hm⟩ := heven
  set P := L.subgroupOf (generalizedFitting G)
  rcases CatLeafProof.evenLieOuterTwoComponentsInput_holds _ τ n f hadm hm σ hσ2 hσout
      (P.subgroupOf (fixedSubgroup σ)) hP.2.2.1 with ⟨τ', n', f', hadm', hm'⟩ | h6 | hU
  all_goals
    obtain ⟨eP⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hP.2.1)
    have hcard : Nat.card (↥(P.subgroupOf (fixedSubgroup σ)) ⧸
        Open.fusionZStar ↥(P.subgroupOf (fixedSubgroup σ))) = 2520 := by
      rw [Nat.card_congr (eP.trans e7).toEquiv]
      exact nat_card_alternating_seven
  · exact lieModel_card_ne_A7 CatLeafProof.lieOrderFormulasInput hadm' hm' hcard
  · obtain ⟨e6⟩ := h6
    rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hcard
    revert hcard
    decide
  · exact lieModel_card_ne_A7 CatLeafProof.lieOrderFormulasInput psu_three_three_admissible hU
      hcard

theorem hs7OuterFact_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hAlt : SolMax.AltPumpSporadicClause) : HS7OuterFact := by
  intro G _ _ hF hcat t ht htF L hLt hL h7 hcyc
  have hnab := generalizedFitting_nonabelian hF h7
  rcases (Milestones.ct_catalog_nonabelian_type_partition _ hnab).mp hcat with
    ⟨n, -, ⟨θ⟩⟩ | hodd | heven | hspor
  · have h9 := eq_nine_of_alternating hF θ ht htF hLt hL h7 hcyc
    subst h9
    exact Or.inl ⟨θ⟩
  · exact (false_of_outer_oddLie hGLS CatLeafProof.lieOrderFormulasInput hF hodd ht htF hLt hL
      h7).elim
  · exact (false_of_outer_evenLie hF heven ht htF hLt hL h7).elim
  · obtain ⟨σ, -, -, hP, he⟩ := exists_outer_properFixedComponent hF ht htF hLt hL h7
    obtain ⟨s, ⟨es⟩⟩ := hspor
    by_cases hs : s = .He
    · subst hs
      exact Or.inr ⟨es⟩
    · exfalso
      have hLN := le_generalizedFitting hF hnab ht hLt hL
      obtain ⟨e7⟩ := nonempty_oddBar_restrict hLN h7
      exact hAlt _ hnab s hs ⟨es⟩ σ _ hP
        (GSThmB.fusionZStar_eq_of_center_eq_bot (center_eq_bot_of_equiv_A7 e7)) 7
        (by decide) le_rfl he

end CFSG.ComponentClassification.HSFLit.HS7
