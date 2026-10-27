module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHCent3D4Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHL2Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHO3Cent

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint


theorem asc82FactCent3_of_d4 (hD4 : Asc82FactCent3D4) : Asc82FactCent3 := by
  intro A _ _ H hH hC hS a ha g hg3 hga
  have hg3' : g ^ 3 = 1 := by
    have h := pow_orderOf_eq_one g
    rwa [hg3] at h
  by_cases hgH : g ∈ H
  · exact fh_cent3_of_f1 H (asc82FactO3Cent_holds A H hH hC hS a ha) hgH hga hg3
  · have hin : FHOdd3Inner ↥H ∨ LieModel ↥H .POmegaPlus 4 3 1 := by
      rcases hS with (h1 | h2 | h3 | h4 | h5 | h6) | (h7 | h8 | h9 | h10)
      · exact Or.inl (fh_odd3Inner_of_tl4 (Or.inl h1))
      · exact Or.inl (fh_odd3Inner_of_tl4 (Or.inr (Or.inl h2)))
      · exact Or.inl (fh_odd3Inner_of_tl4 (Or.inr (Or.inr (Or.inl h3))))
      · exact Or.inl (fh_odd3Inner_of_tl4 (Or.inr (Or.inr (Or.inr (Or.inl h4)))))
      · exact Or.inr h5
      · exact Or.inl (fh_odd3Inner_of_tl4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
      · exact Or.inl (fh_odd3Inner_psl2 (by norm_num) h7)
      · exact Or.inl (fh_odd3Inner_psl2 (dvd_refl 4) h8)
      · exact Or.inl (fh_odd3Inner_of_tl4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))))
      · exact Or.inl (fh_odd3Inner_of_tl4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h10)))))))
    rcases hin with hin | hΩ8
    · exact absurd (fh_mem_of_odd3_inner H hC hin hg3') hgH
    · exact hD4 A H hH hC hΩ8 a ha g hg3 hga hgH

end CFSG.OddStandard.SmallF3.Omega
