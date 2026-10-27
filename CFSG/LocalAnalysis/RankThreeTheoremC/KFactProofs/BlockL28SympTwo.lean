module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Symp
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28NormalSection
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock

theorem kFactCompParabL28TwoRankOn_idxB (hZ : OddCenterRest) :
    KFactCompParabL28TwoRankOn (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB N hNP hPN d₁ d₂ ψ hd₁ hd₂ hψ
  obtain ⟨r, K, _, _, _, -, ⟨φ⟩⟩ := exists_mulEquiv_statedSp_of_idxB hZ hCP.comp hCP.odd hB
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  obtain ⟨β, hker, hpi, hcomm⟩ :=
    sympL28_exists_leviData hI' (fun i hi => (hI i hi).1) htI hmax ρ hρ
  obtain ⟨j₁, j₂, hne, hq₁, hq₂, h₁, h₂⟩ :=
    two_blocks_of_l28Section hCP.parab.1 ρ.toMonoidHom ρ.surjective β hker hpi hcomm
      (spFlagLeviBlock_cases hI' t) hNP hPN ψ hd₁ hd₂ hψ
  exact sympL28_three_le_pRank_of_blocks hI' htI hmax hCP.parab.1 ρ hρ hne hq₁ h₁ hq₂ h₂

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
