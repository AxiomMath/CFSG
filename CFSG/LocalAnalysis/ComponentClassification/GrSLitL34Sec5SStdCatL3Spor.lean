module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatSuzRows
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicThree
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Monster.SteinbergMSporadicOddCoreFree

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem false_of_properFixedComponent_sporadic_psl_three
    (hMinn : CatLeaf.MonsterInnerInput) (hMcomp : CatLeaf.MonsterLocalComponentsInput)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hspor : NativeSporadic.SporadicRep S) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P) {n : ℕ} (hn : 3 ≤ n)
    (hL : LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 n) : False := by
  obtain ⟨s, ⟨e⟩⟩ := hspor
  have hσ := orderOf_eq_two_of_properFixedComponent h
  have hS : IsSimpleGroup S := inferInstance
  have hrow : ∀ {s' : TauCeti.SporadicName}, CatalogueU.SporadicOddCoreFree s' →
      (S ≃* NativeSporadic.Carrier s') → ∃ L : Subgroup (fixedSubgroup σ), IsComponent L ∧
        LieModel (L ⧸ center L) .PSL 3 2 n := fun hs e' => by
    obtain ⟨hL', ⟨eZ⟩⟩ := component_of_properFixedComponent_sporadic hs hna e' h
    exact ⟨_, hL', LieType.CurtisTits.lieModel_of_mulEquiv eZ hL⟩
  by_cases hM : s = .M
  · subst hM
    obtain ⟨L, hL', hLm⟩ := hrow CatalogueU.sporadicOddCoreFree_M e
    exact SeitzReduction.LinearPilot.false_of_monster_PSL hMinn hMcomp hS hna e hσ le_rfl hL' hLm
  have hc : Nat.card (P ⧸ Open.fusionZStar P) = Open.ordA 2 (2 ^ n) :=
    SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hL
  have hdvd : Open.ordA 2 (2 ^ n) ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← hc, ← Nat.card_congr e.toEquiv]
    exact CatLeaf.card_dvd_of_fusionZStar_equiv (Equiv.refl _)
  rcases SeitzReduction.LinearPilot.sl3SporadicResidual_of_dvd (by omega) hM hdvd with
    h1 | ⟨h2, -⟩ | ⟨h4, hs⟩
  · omega
  · omega
  subst h4
  have h16 : ∀ {L : Subgroup (fixedSubgroup σ)}, LieModel (L ⧸ center L) .PSL 3 2 4 →
      Nat.card (L ⧸ center L) = 1425715200 := fun hLm => by
    rw [SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hLm]
    decide
  rcases hs with rfl | rfl | rfl
  · obtain ⟨L, hL', hLm⟩ := hrow CatalogueU.sporadicOddCoreFree_Fi23 e
    have h11 := SeitzReduction.OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hσ hL'
    rw [h16 hLm] at h11
    norm_num at h11
  · obtain ⟨L, hL', hLm⟩ := hrow CatalogueU.sporadicOddCoreFree_Fi24Prime e
    rcases SeitzReduction.OmegaPilot.fi24_card_quotient_center hS hna e hσ hL' with h1 | h1 | h1 <;>
      rw [h16 hLm] at h1 <;> norm_num at h1
  · obtain ⟨L, hL', hLm⟩ := hrow BMCase.sporadicOddCoreFree_B e
    rcases SeitzReduction.OmegaPilot.baby_card_quotient_center hS hna e hσ hL' with h1 | h1 <;>
      rw [h16 hLm] at h1 <;> norm_num at h1

end CFSG.ComponentClassification.GrSLit.L34Sec5S
