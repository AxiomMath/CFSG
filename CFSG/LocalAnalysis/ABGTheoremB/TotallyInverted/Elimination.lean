module

public import CFSG.LocalAnalysis.ABGTheoremB.IV6
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstruction
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalAssembly
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.InputsFourFusion
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.NoDataBridge
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusW

public section

namespace CFSG.ABGTheoremB.TotallyInverted

variable {G : Type} [Group G] [Finite G] {σ : Setting G}

theorem not_totallyInverted_of_height_ne_one (hσ : σ.IsValid) (hh : σ.height ≠ 1)
    (hII : σ.ChapterIIFacts) (hV : σ.CorollaryV61) (hT : σ.TIFacts) (hQC : σ.QCoverFact)
    (hD : Sec10.DGroupFourFusion G) (hI : ∀ (r : ℕ) (Δ : Data σ r), Sec11.Inputs Δ) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Exceptional r → ¬ σ.TotallyInverted r := by
  intro r hr hdvd hexc hti
  obtain ⟨Δ⟩ := nonempty_data hσ hh hII.automizer_T hV hT hr hdvd hexc hti
  exact no_data_of_inputs hσ hII Δ
    (omnibusInputs_of hσ hh hII hT hQC (Inputs.abg_II_3_1_input G) Δ)
    (abg_IV_6_2_of_propIV62 (σ.propIV62 hσ hII) hr hdvd) (Inputs.qGroupFourFusion G) hD
    (hI r Δ)

end CFSG.ABGTheoremB.TotallyInverted
