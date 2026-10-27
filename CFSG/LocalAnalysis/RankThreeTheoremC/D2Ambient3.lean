module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Roadmap3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem aglGlobal_of_setting (hS : Setting G) : AGLGlobal G :=
  ⟨hS.simple, hS.nonab, hS.kProper, hS.charTwo, hS.rank.ge, glbPreuniqueness_of_setting hS⟩

theorem d1At_of_theoremD1 (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) :
    D1At G p :=
  fun Q M hM hcore H hH h3 => hD1 p hp Q M hM.1 hcore (fun K hK _ hMK => hM.2 K hK hMK) H hH h3

theorem noXBlockFor_of_setting (h : D1NoXBlock3 G) (hS : Setting G) : NoXBlockFor G :=
  h hS

end CFSG.LocalAnalysis.RankThreeTheoremC
