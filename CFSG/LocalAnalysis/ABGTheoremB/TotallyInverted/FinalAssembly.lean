module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalPGroupR
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalNoData
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Omnibus
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.NotPGroup
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Transitivity

public section

namespace CFSG.ABGTheoremB.TotallyInverted

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem pGroupR_of_omnibus (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (homni : Omnibus Δ) (hI : Sec11.Inputs Δ) : PGroupR Δ :=
  pGroupR hσ hF Δ homni (conjugateMaximalTC hσ Δ homni) hI

theorem no_data_of_inputs (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hO : OmnibusInputs Δ) (h462 : ABG_IV_6_2 σ r) (hQ : Sec10.QGroupFourFusion G)
    (hD : Sec10.DGroupFourFusion G) (hI : Sec11.Inputs Δ) : False := by
  have homni := omnibus hσ hF Δ hO
  have h92 := notPGroupP hσ hF Δ homni h462
  exact no_data hσ Δ h92 (transitivity hσ hF Δ homni h92 hQ hD)
    (pGroupR_of_omnibus hσ hF Δ homni hI)

end CFSG.ABGTheoremB.TotallyInverted
