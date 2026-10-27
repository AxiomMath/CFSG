module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotSwapMain
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeExists

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)


@[expose] def E7NormalizationInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K), orderOf σ = 2 →
    4 ≤ Nat.card (fixSubfield σ) → NormalizationProperty (leviInclusion σ .high)

theorem e7FieldRowFamilyInput_of_normalization (h : E7NormalizationInput) :
    E7FieldRowFamilyInput := by
  intro G _ _ L K₂ _ _ _ σ e t hψ htL ht2 hσ hfix hq
  obtain ⟨φ, hφ⟩ := exists_isFieldRowFamily hq (h K₂ σ hσ hq) hψ htL ht2 hfix
  exact ⟨φ, ⟨hφ.compatible, hφ.range_eq, hφ.fix⟩⟩

theorem seitzExclusion_highE7_of_normalization (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaPilot.OmegaNotOddLieInputAt 6) (hSpor : OmegaPilot.CatOmegaSporadicAt 6)
    (hN : E7NormalizationInput) (h2 : E7TwoInput) :
    SeitzExclusion (HighExceptional .E7) :=
  seitzExclusion_highE7_of_five_inputs hGLS hXodd hSpor
    (e7FieldRowFamilyInput_of_normalization hN) h2

end CFSG.SeitzReduction.E7Pilot
