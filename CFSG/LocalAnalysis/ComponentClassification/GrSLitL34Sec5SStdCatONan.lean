module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatSuzRows
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatSOOrd
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint

variable {S : Type} [Group S] [Finite S]

theorem not_card_onan_of_properFixedComponent_sporadic
    (hMinn : CatLeaf.MonsterInnerInput) (hMcomp : CatLeaf.MonsterLocalComponentsInput)
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hspor : NativeSporadic.SporadicRep S)
    {σ : MulAut S} {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P) :
    Nat.card (P ⧸ Open.fusionZStar P) ≠ 460815505920 := by
  intro hP
  obtain ⟨s, ⟨e⟩⟩ := hspor
  have hσ := orderOf_eq_two_of_properFixedComponent h
  have hS : IsSimpleGroup S := inferInstance
  have hdvd : 460815505920 ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← hP, ← Nat.card_congr e.toEquiv]
    exact CatLeaf.card_dvd_of_fusionZStar_equiv (Equiv.refl _)
  cases s
  case ONan =>
    have hcard : Nat.card P = Nat.card S := by
      refine Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card P) ?_
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .ONan) = 460815505920
        from Sporadic.ON.card_ON, ← hP]
      exact Subgroup.card_quotient_dvd_card _
    exact h.2.2.2 (Subgroup.eq_top_of_card_eq P hcard)
  case M =>
    obtain ⟨hL, ⟨eZ⟩⟩ := component_of_properFixedComponent_sporadic
      CatalogueU.sporadicOddCoreFree_M hna e h
    have h1 := (SeitzReduction.OmegaPilot.monster_two_part_card_quotient_center hMinn hMcomp hS
      hna e hσ hL).1
    rw [← Nat.card_congr eZ.toEquiv, hP] at h1
    exact absurd h1 (by norm_num)
  all_goals exact not_dvd_card_carrier_onan (by decide) (by decide) hdvd

end CFSG.ComponentClassification.GrSLit.L34Sec5S
