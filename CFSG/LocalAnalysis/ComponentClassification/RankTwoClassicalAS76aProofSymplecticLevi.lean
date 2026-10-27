module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpBlocks
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

theorem spBarW_le_centralizer_spBarL {K : Type} [Field K] {m : ℕ} :
    spBarW K m ≤ centralizer (spBarL K m : Set (StatedProj (StatedSp (m + 1) K))) := fun _ hw =>
  mem_centralizer_iff.mpr fun _ hl => (spBarW_commute_spBarL hw hl).symm

end CFSG.ComponentClassification.RankTwoClassical
