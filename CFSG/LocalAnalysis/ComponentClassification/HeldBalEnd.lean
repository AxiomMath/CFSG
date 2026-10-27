module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStatements

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

theorem heldKNormalStepBal_of_inputs (hLay : HeldTwoALayerFact) (hAK : HeldTwoAKFact)
    (hInv : HeldInvolAutFact) (hFact : L34InvolutionCentralizerFact)
    (hComp : HeldKComponentStepBal) : HeldKNormalStepBal :=
  fun X _ _ L hset hbal u hu =>
    heldKNormalAt_of_inputs hLay hAK hInv hFact hset hu (hComp X L hset hbal u hu)

theorem heldEndStepBal_of_steps (hKN : HeldKNormalStepBal)
    (hEnd : HeldZStarEndStep) (hB : HeldTwoBCentralizerFact) (hLay : HeldTwoALayerFact)
    (hFour : HeldTwoAFourFact) (hClass : HeldTwoAClassFact) (hPair : HeldTwoAPairFact)
    (hGen : HeldTwoAGenerationFact) : HeldEndStepBal := by
  intro X _ _ L hset hbal hW hstd he hrank
  have hS : HeldEndSetting X L := ⟨hset, hW, hstd, he, hrank⟩
  have hK := hKN X L hS hbal
  have h36 : ∀ v ∈ L, orderOf v = 2 → ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({v} : Set X) →
      (K₁.subgroupOf (centralizer ({v} : Set X))).Normal →
      (∃ u : X, HeldTwoA L u ∧ Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u))) → HeldTwoA L v :=
    fun _ hvL hv _ h1 h2 h3 => heldLemma36 hB hLay hFour hS hK hvL hv h1 h2 h3
  exact hEnd X L hS hK h36 (fun _ hu => heldCor37 hClass hPair hGen hS hK h36 hu)

end CFSG.ComponentClassification.GrSLit
