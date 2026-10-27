module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.CatFS46
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreFixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreON
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreSuz
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreHe
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableSuzON
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableHeLy

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.Induction.SporCentre


theorem sol78Thm46SporL34Centre_holds : Sol78Thm46SporL34Centre := by
  intro S _ _ hS hna σ hσ Q hQF hQ hQne hZ hL
  have hPF : ComponentClassification.CatLeaf.ProperFixedComponent σ Q := ⟨hσ, hQF, hQ, hQne⟩
  have hσ2 : orderOf σ = 2 := orderOf_eq_two hPF
  have hD := isComponent_of_isPComponent hQF hQ hZ
  have hcard : Nat.card ((Q.subgroupOf (fixedSubgroup σ)) ⧸ center (Q.subgroupOf
      (fixedSubgroup σ))) = 20160 := by
    rw [card_quotient_center_subgroupOf hQF]
    obtain ⟨f⟩ := ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL
    rw [Nat.card_congr f.toEquiv]
    exact ComponentClassification.PSL3Four.card_S
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨e⟩
    have hrows := ComponentClassification.CatFC.sporadic_rows_suz hS hna e hσ2 hD
    by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨t, ht⟩ := hin
      obtain ⟨ht2, hQC, hcomp⟩ := inner_data hna hPF hZ ht.symm
      have hbot : center Q = ⊥ := center_eq_bot_of_component_suz e ht2 hQC hcomp
      exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot) hL
    · have h := hrows.2 hin
      rw [hcard] at h
      simp only [ComponentClassification.CatFC.SporadicOuterRow] at h
      omega
  ·
    rintro ⟨e⟩
    have hrows := ComponentClassification.CatFC.sporadic_rows_he hS hna e hσ2 hD
    by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨t, ht⟩ := hin
      obtain ⟨ht2, hQC, hcomp⟩ := inner_data hna hPF hZ ht.symm
      exact nonempty_center_equiv_kleinFour e ht2 hQC hcomp
    · have h := hrows.2 hin
      rw [hcard] at h
      simp only [ComponentClassification.CatFC.SporadicOuterRow] at h
      omega
  ·
    rintro ⟨e⟩
    have hrows := ComponentClassification.CatFC.sporadic_rows_onan hS hna e hσ2 hD
    by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨t, ht⟩ := hin
      obtain ⟨ht2, hQC, hcomp⟩ := inner_data hna hPF hZ ht.symm
      exact nonempty_center_equiv_zmod_four e ht2 hQC hcomp
    · have h := hrows.2 hin
      rw [hcard] at h
      simp only [ComponentClassification.CatFC.SporadicOuterRow] at h
      omega

end CFSG.EvenSporadicStandard.Induction
