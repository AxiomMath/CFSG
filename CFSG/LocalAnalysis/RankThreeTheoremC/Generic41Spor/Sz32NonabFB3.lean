module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB3h
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB3a
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB3g
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB3i

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Part

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y} {L : Subgroup Y} {z : Y}

theorem nf5_L_le (h9 : KFactNoM125Sylow') (h714 : KFactI714Four') (h10 : KFactFieldGeneration5)
    (hSz : Sz32Facts) (hSig : Sz32SigOne) (hc : NF5Cfg F Γ B R₀ x L z) : L ≤ Γ := by
  have hFL := nf5_F_not_le h9 hc
  have hI := nf5_I714 h714 hc hFL
  have hnS := nf5_not_suzuki hSz hSig hc
  exact nf5_L_le_Γ hc (nf5_generation h10 hc hI hnS)

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
