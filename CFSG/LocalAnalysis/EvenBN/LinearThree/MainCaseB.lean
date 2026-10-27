module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.Main
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBUnique
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBFactors

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (projRad)

theorem caseBSwapFactors :
    CaseBSwapFactors := by
  intro G _ _ A f h d K _ _ _ F hKc w₀ w₁ hB₀ hB₁
  have hR : Radicals d.V ((projRad K 0).map F.φ) ((projRad K 1).map F.φ) (2 ^ f) :=
    hKc ▸ F.radicals
  obtain ⟨N₀⟩ := h.exists_caseBNotation d hR (Or.inl rfl) w₀ (F.leviData 0) hKc hB₀
  obtain ⟨N₁⟩ := h.exists_caseBNotation d hR (Or.inr rfl) w₁ (F.leviData 1) hKc hB₁
  have hf2 : 2 ≤ f := by have := h.three_le; omega
  obtain ⟨N₁', hq, h₁₂, hδ, hsurj, hM₀, hM₁⟩ := N₀.exists_swapFactors N₁ hKc hf2 hKc
  exact ⟨_, hq, h₁₂, h.unique_of_caseB hKc N₀ N₁' hB₀ hB₁ hq h₁₂ hδ hsurj hM₀ hM₁⟩

section Certified


theorem ctt_bn_psl3_of_exclusions (hL3 : LinearThreeExclusion27) (hG23 : G2ThreeExclusion27)
    (hA : CaseAExclusion) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 3 2 f :=
  ctt_bn_psl3_of_inputs hL3 hG23 hA caseBSwapFactors

end Certified

end CFSG.LocalAnalysis.EvenBN.LinearThree
