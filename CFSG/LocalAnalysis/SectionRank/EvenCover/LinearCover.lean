module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap

public section

namespace CFSG.SectionRank.EvenCover

open CFSG.Assembly.LowTwoRank

theorem even_linear_perfect_odd_cover_map
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL n K)) :
    ∃ φ : StatedSL n K →* L, Function.Surjective φ ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) ∧
      ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)).map φ = Subgroup.center L := by
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ := even_linear_central_odd_extension_splitting_stated hn hsurj hcen
    (Odd.of_dvd_nat hodd hdvd)
  exact perfect_cover_map_of_section e σ hσ

end CFSG.SectionRank.EvenCover
