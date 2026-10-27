module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma411

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

@[expose] def SectionFourAfter411 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (h : Standing t L p f),
      (∀ (t' : X) (L' : Subgroup X) (p' f' : ℕ), Config t' L' p' f' →
        twoPart (centralizer ({t'} : Set X)) ≤ twoPart (centralizer ({t} : Set X))) →
      ∀ (S : Subgroup X) (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (w z : X),
        Standing.Setup42 h hS w z →
      ∀ V : Subgroup X,
        IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) →
        S ≤ V →
      ∀ β : X, IsBeta411 t L S w z V β →
        (∀ β' : X, IsBeta411 t L S w z V β' →
          twoPart (centralizer ({β'} : Set X)) ≤ twoPart (centralizer ({β} : Set X))) →
        (IsBeta411 t L S w z V (w ^ (orderOf w / 2)) ∧
          twoPart (centralizer ({β} : Set X)) ≤
            twoPart (centralizer ({w ^ (orderOf w / 2)} : Set X)) →
          β = w ^ (orderOf w / 2)) →
        False

theorem sectionFourAfter42_of_after411 (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (h411 : SectionFourAfter411) : SectionFourAfter42 := by
  intro X _ _ _ hnonab hK hcat t L p f h hmax S hS w z hσ
  classical
  obtain ⟨V, hV, hSV⟩ := exists_isSylowOf_ge hS.isPGroup hσ.S_le_normalizer_T
  obtain ⟨β₀, hβ₀⟩ := hσ.exists_isBeta411 hKF hKC h.sect hV hSV
  obtain ⟨β₁, hβ₁, hmax₁⟩ := Set.exists_max_image {β : X | IsBeta411 t L S w z V β}
    (fun β => twoPart (centralizer ({β} : Set X))) (Set.toFinite _) ⟨β₀, hβ₀⟩
  by_cases hu : IsBeta411 t L S w z V (w ^ (orderOf w / 2)) ∧
      twoPart (centralizer ({β₁} : Set X)) ≤ twoPart (centralizer ({w ^ (orderOf w / 2)} : Set X))
  · exact h411 X hnonab hK hcat t L p f h hmax S hS w z hσ V hV hSV _ hu.1
      (fun β' hβ' => (hmax₁ β' hβ').trans hu.2) fun _ => rfl
  · exact h411 X hnonab hK hcat t L p f h hmax S hS w z hσ V hV hSV β₁ hβ₁ hmax₁
      fun hu' => absurd hu' hu

theorem harrislit_of_inputs_411 (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hGH : UFrontier.GH74ModelsInput) (hHSF : GSLit.HarrisSolomonFritzInput)
    (hHS : HarrisSolomonDihedralInput) (hKG : AutPSL2SylowInput)
    (hKC : AutPSL2CentralizerInput) (hKF : AutPSL2FusionInput)
    (h411 : SectionFourAfter411) : GSLit.HarrisInput :=
  harrislit_of_inputs hCU hGH hHSF hHS hKG (sectionFourAfter42_of_after411 hKF hKC h411)

end CFSG.ComponentClassification.HarrisLit
