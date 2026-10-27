module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSetup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma42

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

@[expose] def SectionFourAfter42 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (h : Standing t L p f),
      (∀ (t' : X) (L' : Subgroup X) (p' f' : ℕ), Config t' L' p' f' →
        twoPart (centralizer ({t'} : Set X)) ≤ twoPart (centralizer ({t} : Set X))) →
      ∀ (S : Subgroup X) (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (w z : X),
        Standing.Setup42 h hS w z → False

theorem sectionFour_of_after42 (hKG : AutPSL2SylowInput) (h42 : SectionFourAfter42) :
    SectionFour := by
  intro X _ _ _ hnonab hK hcat hsect t L p f hc hmax hD h16
  have h : Standing t L p f := ⟨hc, hD, h16, hsect⟩
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (centralizer ({t} : Set X))
  obtain ⟨w, z, hσ⟩ := h.exists_setup42 hKG hS
  exact h42 X hnonab hK hcat t L p f h hmax S hS w z hσ

theorem harrislit_of_inputs (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hGH : UFrontier.GH74ModelsInput) (hHSF : GSLit.HarrisSolomonFritzInput)
    (hHS : HarrisSolomonDihedralInput) (hKG : AutPSL2SylowInput)
    (h42 : SectionFourAfter42) : GSLit.HarrisInput :=
  harrisInput_of_sectionFour hCU hGH hHSF hHS (sectionFour_of_after42 hKG h42)

end CFSG.ComponentClassification.HarrisLit
