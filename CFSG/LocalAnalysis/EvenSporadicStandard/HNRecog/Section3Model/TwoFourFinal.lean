module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TwoFourSpec

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

section Cert


theorem suborbitFacts_two_four :
    ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
      ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → TwoFourData (Gx z₁) := by
  intro H _ E h a z b z₁ hf
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  obtain ⟨Ψ₀, -⟩ := exists_mulEquiv_p1408_of_isF5Centralizer h
  have hΨz₁ : IsConj pZ₁ (Ψ₀ z₁) := by
    refine isConj_pZ₁_of_natCard hP (by rw [MulEquiv.orderOf_eq, hf.orderOf_z₁]) ?_
    rw [show Nat.card ↥(centralizer ({Ψ₀ z₁} : Set ↥P1408)) = Nat.card ↥(Gx z₁) from
      natCard_Gx_map Ψ₀ z₁]
    exact natCard_of_isShapeTwoTwoTimesTwoFourA5 hf.cent_z₁
  obtain ⟨g, hg⟩ := isConj_iff.mp hΨz₁.symm
  let Ψ : H ≃* ↥P1408 := Ψ₀.trans (MulAut.conj g)
  have hΨ : Ψ z₁ = pZ₁ := by simpa [Ψ] using hg
  have hf_inj : Function.Injective (P1408.subtype.comp Ψ.toMonoidHom) :=
    P1408.subtype_injective.comp Ψ.injective
  have hmap : (Gx z₁).map (P1408.subtype.comp Ψ.toMonoidHom) =
      P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))) := by
    rw [← Subgroup.map_map, TwoHSData.map_centralizer_singleton Ψ z₁, hΨ]
    exact map_subtype_centralizer P1408 pZ₁
  have hmodel := twoFourData_model hP
  rw [← hmap] at hmodel
  exact TwoFourData.of_map hf_inj hmodel

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3
