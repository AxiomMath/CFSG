module

public import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.LocalAnalysis.SectionRank.OddCover.Symplectic
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.QuasisimpleCatalog

public section

namespace CFSG.SectionRank.OddCover

open CFSG.Assembly.LowTwoRank

theorem catalog_classical_odd {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L)
    (hSQT : IsStronglyQuasithin L) (hodd : Odd (Nat.card (Subgroup.center L)))
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : StatedClassicalModel (L ⧸ Subgroup.center L) t n p f) : CatalogStepConclusion L := by
  have : Fact p.Prime := ⟨hp⟩
  have hG := isStronglyQuasithin_iff.1 hSQT
  rcases classical_odd_central_quotient_bound hG (Subgroup.center L) le_rfl hp2 h with
    ⟨rfl, (⟨rfl, -⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, rfl⟩
  · exact (odd_linear_two_odd_cover_catalog_step hp hp2 hL hSQT hodd h).1
  · exact prime_classical_three_odd_cover_catalog_step hp hp2 (Or.inl rfl) hL hSQT hodd h
  · obtain ⟨-, hf, hr⟩ := classical_model_rank hp2 h
    have h3 := pRank_quotient_le_three hp2 (hG p hp hp2) (Subgroup.center L) le_rfl
    have hf1 : f = 1 := by
      rcases hr with ⟨ht, -⟩ | ⟨-, (⟨-, hr⟩ | hr)⟩ | ⟨ht, -⟩ | hr
      · cases ht
      · omega
      · omega
      · cases ht
      · omega
    subst hf1
    exact prime_classical_three_odd_cover_catalog_step hp hp2 (Or.inr rfl) hL hSQT hodd h
  · exact absurd hSQT (odd_symplectic_central_cover_rank_three (Subgroup.center L) le_rfl hp2 h).2

theorem catalogClassicalOddHyp : CatalogClassicalOddHyp :=
  fun _ _ _ hL hSQT hodd _ _ _ _ hp hp2 h => catalog_classical_odd hL hSQT hodd hp hp2 h

end CFSG.SectionRank.OddCover
