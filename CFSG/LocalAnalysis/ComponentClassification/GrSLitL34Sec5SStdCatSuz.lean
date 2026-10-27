module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatSuzRows
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatSOOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {S : Type} [Group S] [Finite S]

theorem not_card_suz_of_properFixedComponent_sporadic
    (hMinn : CatLeaf.MonsterInnerInput) (hMcomp : CatLeaf.MonsterLocalComponentsInput)
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hspor : NativeSporadic.SporadicRep S)
    {σ : MulAut S} {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P) :
    Nat.card (P ⧸ Open.fusionZStar P) ≠ 448345497600 := by
  intro hP
  obtain ⟨s, ⟨e⟩⟩ := hspor
  have hσ := orderOf_eq_two_of_properFixedComponent h
  have hS : IsSimpleGroup S := inferInstance
  have hdvd : 448345497600 ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← hP, ← Nat.card_congr e.toEquiv]
    exact CatLeaf.card_dvd_of_fusionZStar_equiv (Equiv.refl _)
  have hrow : ∀ {s' : TauCeti.SporadicName}, CatalogueU.SporadicOddCoreFree s' →
      (S ≃* NativeSporadic.Carrier s') → ∃ L : Subgroup (fixedSubgroup σ), IsComponent L ∧
        Nat.card (L ⧸ center L) = 448345497600 := fun hs e' => by
    obtain ⟨hL, ⟨eZ⟩⟩ := component_of_properFixedComponent_sporadic hs hna e' h
    exact ⟨_, hL, (Nat.card_congr eZ.toEquiv).symm.trans hP⟩
  cases s
  case Suz =>
    have hcard : Nat.card P = Nat.card S := by
      refine Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card P) ?_
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Suz) = 448345497600
        from Sporadic.Suz.card_Suz, ← hP]
      exact Subgroup.card_quotient_dvd_card _
    exact h.2.2.2 (Subgroup.eq_top_of_card_eq P hcard)
  case Fi22 =>
    obtain ⟨L, hL, hc⟩ := hrow CatalogueU.sporadicOddCoreFree_Fi22 e
    rcases card_quotient_center_of_fi22 hS hna e hσ hL with h1 | h1 | h1 <;> rw [hc] at h1 <;>
      norm_num at h1
  case Fi23 =>
    obtain ⟨L, hL, hc⟩ := hrow CatalogueU.sporadicOddCoreFree_Fi23 e
    rcases card_quotient_center_of_fi23 hS hna e hσ hL with h1 | h1 <;> rw [hc] at h1 <;>
      norm_num at h1
  case Fi24Prime =>
    obtain ⟨L, hL, hc⟩ := hrow CatalogueU.sporadicOddCoreFree_Fi24Prime e
    rcases SeitzReduction.OmegaPilot.fi24_card_quotient_center hS hna e hσ hL with h1 | h1 | h1 <;>
      rw [hc] at h1 <;> norm_num at h1
  case Co1 =>
    obtain ⟨L, hL, hc⟩ := hrow CatalogueU.sporadicOddCoreFree_Co1 e
    have h1 := card_quotient_center_of_co1 hS hna e hσ hL
    rw [hc] at h1
    norm_num at h1
  case B =>
    obtain ⟨L, hL, hc⟩ := hrow BMCase.sporadicOddCoreFree_B e
    rcases SeitzReduction.OmegaPilot.baby_card_quotient_center hS hna e hσ hL with h1 | h1 <;>
      rw [hc] at h1 <;> norm_num at h1
  case M =>
    obtain ⟨L, hL, hc⟩ := hrow CatalogueU.sporadicOddCoreFree_M e
    have h1 := (SeitzReduction.OmegaPilot.monster_two_part_card_quotient_center hMinn hMcomp hS
      hna e hσ hL).1
    rw [hc] at h1
    exact absurd h1 (by norm_num)
  all_goals
    exact not_dvd_card_carrier_suz (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hdvd

end CFSG.ComponentClassification.GrSLit.L34Sec5S
