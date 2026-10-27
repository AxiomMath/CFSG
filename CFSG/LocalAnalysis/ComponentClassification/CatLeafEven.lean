module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueEvenExceptionalCheck
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepOne
public import CFSG.Sporadic.Schreier.LargeReeExcl
import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem uOutcome_of_evenLieType {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnonab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (heven : EvenLieType (GeneralizedFitting.subgroup X))
    (hz : ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) :
    OutcomeLocal.UOutcome X := by
  have hF : CFSG.generalizedFitting X = GeneralizedFitting.subgroup X :=
    CFSG.generalizedFitting_eq_componentClassification X
  have hsimple' : IsSimpleGroup (CFSG.generalizedFitting X) := hF ▸ hsimple
  have hnonab' : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := hF ▸ hnonab
  obtain ⟨z, hz2, hcore⟩ := hz
  obtain ⟨t, n, f, hadm, hmodel⟩ := heven
  rcases hmodel with ⟨ht, hcl⟩ | ⟨-, ht, hex⟩ | ⟨-, ht, hrt⟩ | ⟨-, rfl, hsz⟩
  · have hcl' : StatedClassicalModel (CFSG.generalizedFitting X) t n 2 f := hF ▸ hcl
    simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨hlt, hcase, -, -⟩ :=
        UnbalancedCatalog.even_linear_almost_simple_unbalanced_outcome hnonab' hcl'
          ⟨z, hz2, hcore⟩
      rw [hF] at hlt hcase
      rcases hcase with hodd | h322
      · exact .inl hodd
      · exact .inr (.inr ⟨.inl (.inl ⟨by decide, h322⟩), hlt⟩)
    · exact absurd ((UnbalancedCatalog.even_unitary_almost_simple_odd_core_vanishing hnonab'
        hcl').2 z hz2) hcore
    · exact absurd ((UnbalancedCatalog.even_symplectic_almost_simple_odd_core_vanishing hnonab'
        hcl').1 z hz2) hcore
    · obtain ⟨-, -, -, hp2⟩ := hcl.1
      exact absurd rfl hp2
    · exact absurd ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
        _ (.inl rfl) hcl').2 z hz2) hcore
    · exact absurd ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
        _ (.inr rfl) hcl').2 z hz2) hcore
  · exact CatalogueU.evenExceptionalCheck X hsimple hnonab t f ht hex ⟨z, hz2, hcore⟩
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact absurd hadm.2.2.2.1 (by norm_num)
    · exact absurd ⟨z, hz2, hcore⟩
        (Sporadic.Schreier.LargeReeExcl.CTU_catalog_large_Ree_Tits_check X hsimple hnonab _ f
          (.inl rfl) hrt)
    · exact absurd ⟨z, hz2, hcore⟩
        (Sporadic.Schreier.LargeReeExcl.CTU_catalog_large_Ree_Tits_check X hsimple hnonab _ f
          (.inr rfl) hrt)
  · have hsz' : SuzukiModel (CFSG.generalizedFitting X) 2 f := hF ▸ hsz
    exact absurd (UnbalancedGS.catalog_suzuki_almost_simple_odd_core_vanishing hsimple' hnonab'
      hsz' z hz2).2.2 hcore

theorem generalizedFitting_subgroup_eq_top_of_simple {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] : GeneralizedFitting.subgroup X = ⊤ :=
  (CFSG.generalizedFitting_eq_componentClassification X).symm.trans
    (CFSG.Adapters.generalizedFitting_eq_top_of_isSimpleGroup X)

theorem oddCore_eq_bot_or_uList_of_evenLieType {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S) {t : S} (ht : orderOf t = 2) :
    CFSG.oddCore (centralizer ({t} : Set S)) = ⊥ ∨ TBLit.UList S := by
  by_cases hcore : CFSG.oddCore (centralizer ({t} : Set S)) = ⊥
  · exact .inl hcore
  right
  have hFt : GeneralizedFitting.subgroup S = ⊤ := generalizedFitting_subgroup_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup S ≃* S := (MulEquiv.subgroupCongr hFt).trans topEquiv
  have : IsSimpleGroup (GeneralizedFitting.subgroup S) := eF.isSimpleGroup
  have hnab : ∃ a b : GeneralizedFitting.subgroup S, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eF.symm x, eF.symm y, fun h => hxy (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨τ, n, f, hadm, hm⟩ := heven
  exact TBLit.uList_of_mulEquiv eF (TBLit.uList_of_uOutcome (uOutcome_of_evenLieType inferInstance
    hnab ⟨τ, n, f, hadm, LieType.CurtisTits.lieModel_of_mulEquiv eF.symm hm⟩ ⟨t, ht, hcore⟩))

theorem not_isHeldType_of_properFixedComponent_evenLie (hEO : EvenLieOuterTwoComponentsInput)
    (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) :
    ¬ GrSLit.IsHeldType (P ⧸ Open.fusionZStar P) ∨ TBLit.UList S := by
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · refine .inl fun _ => ?_
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    · exact .inr hU
  ·
    refine .inl ?_
    rintro ⟨eH⟩
    obtain ⟨τ, n, f, hadm, hm⟩ := heven
    obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
    have hcard : Nat.card ((P.subgroupOf (fixedSubgroup σ)) ⧸
        Open.fusionZStar (P.subgroupOf (fixedSubgroup σ))) = 4030387200 := by
      rw [Nat.card_congr (eL.trans eH).toEquiv, Sporadic.He.card_He]
    rcases hEO S τ n f hadm hm σ hσ2 hout _ h.2.2.1 with ⟨τ', n', f', hadm', hm'⟩ | hA | hU
    · exact lieModel_card_ne_held hO hadm' hm' hcard
    · obtain ⟨eA⟩ := hA
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcard
      norm_num [Nat.factorial] at hcard
    · have hadm3 : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      exact lieModel_card_ne_held hO hadm3 hU hcard

end CFSG.ComponentClassification.CatLeaf
