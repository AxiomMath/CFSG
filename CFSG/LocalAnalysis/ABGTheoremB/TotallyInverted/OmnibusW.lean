module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusWQ

public section

namespace CFSG.ABGTheoremB.TotallyInverted

theorem omnibusInputs_of {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}
    (hσ : σ.IsValid) (hh : σ.height ≠ 1) (hII : σ.ChapterIIFacts) (hT : σ.TIFacts)
    (hQC : σ.QCoverFact) (h31 : ABG_II_3_1_Input G) (Δ : Data σ r) : OmnibusInputs Δ where
  nStructure := OmnibusW.nStructure hσ hh hT Δ
  qCentralizer := h31
  dCentralizer := fun h => absurd h hh
  qConjugacy := OmnibusW.qConjugacy hσ hh hII hT hQC h31 Δ
  dConjugacy := fun h => absurd h hh

end CFSG.ABGTheoremB.TotallyInverted
