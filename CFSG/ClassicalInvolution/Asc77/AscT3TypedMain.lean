module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedG2D4
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.G2D4Models

variable {p f : ℕ} [Fact p.Prime]

theorem thm3SectBelow_of_citBelowU (hM : G2D4MaxNormalizer p) {n : ℕ} (hn : CITBelowU p f n) :
    Thm3SectBelow p f n := by
  intro hp hq Y _ _ hY Λ hΛ hdis L hL
  by_contra hnA
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hnA
  obtain ⟨a, hQ⟩ := quotViol_of_aViol hp hq hΛ hL hv
  have hΛb : HypOmegaMod p f (oddQuotientFamily Λ) :=
    oddQuotHyp p f hp hq Y Λ hΛ (classicalInvolutionOddCore Y)
      (CFSG.ComponentClassification.OddCore.odd_card Y)
  have hO : classicalInvolutionOddCore (Y ⧸ classicalInvolutionOddCore Y) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  have hlt : Nat.card (Y ⧸ classicalInvolutionOddCore Y) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hY
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΛb.conjInvariant hΛb.classical
    ⟨_, mem_oddQuotientFamily hL⟩ hO hlt
  exact hdis (hQ.dstarConnected hM hp hq hΛb D)

theorem h3s_of_maxNormalizer (hM : G2D4MaxNormalizer p) :
    ∀ n, CITBelowU p f n → Thm3SectBelow p f n :=
  fun _ hn => thm3SectBelow_of_citBelowU hM hn

end CFSG.ClassicalInvolution.Asc77.T3Typed
