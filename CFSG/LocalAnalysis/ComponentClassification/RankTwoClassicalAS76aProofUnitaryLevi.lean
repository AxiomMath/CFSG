module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

theorem uBarW_le_centralizer_uBarL {K : Type} [Field K] {k f : ℕ} :
    uBarW K k f ≤ centralizer (uBarL K k f : Set (StatedProj (StatedSU (2 + k) (2 ^ f) K))) :=
  fun _ hw => mem_centralizer_iff.mpr fun _ hl => (uBarW_commute_uBarL hw hl).symm

theorem uBarT_le_centralizer_uBarL {K : Type} [Field K] {f : ℕ} :
    uBarT K f ≤ centralizer (uBarL K 2 f : Set (StatedProj (StatedSU (2 + 2) (2 ^ f) K))) :=
  fun _ ht => mem_centralizer_iff.mpr fun _ hl => (uBarT_commute_uBarL ht hl).symm

end CFSG.ComponentClassification.RankTwoClassical
