module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Reduce
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.StrongThreeSolv
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Quotient

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kFactStrongThreeSolv_of_gls3 (hSch : SchreierFor CFSG.Assembly.InCatalog)
    (hG : Gls3StronglyThreeEmbedded) : CFSG.AGLEmbeddingD2.McLaughlin.KFactStrongThreeSolv := by
  intro N _ _ hN N₀ hstr h2 Y hYN₀ hY h3
  obtain ⟨E, hEM, hE, hcard⟩ := exists_elemAbelian_coreImage hstr h2
  have D : CoreFree (coreImage N₀) E :=
    ⟨stronglyEmbedded_coreImage hstr, normalCore_coreImage, hEM, hE, hcard⟩
  have hX := isKGroup_quotient hN N₀.normalCore
  have hbot : Y.map (coreMk N₀) = ⊥ := by
    refine perfect_eq_bot_of_coreFree hSch hG hX D (Subgroup.map_mono hYN₀) ?_
    rw [← Subgroup.map_commutator, hY]
  have hYC : Y ≤ N₀.normalCore := fun y hy => by
    have : coreMk N₀ y ∈ Y.map (coreMk N₀) := ⟨y, hy, rfl⟩
    rw [hbot] at this
    simpa [coreMk] using this
  exact not_dvd_card_normalCore hstr (h3.trans (Subgroup.card_dvd_of_le hYC))

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
