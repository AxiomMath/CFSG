module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Setting

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem catalog_of_chev3 {G : Type} [Group G] (h : Chev3 G) : Catalog G := by
  obtain ⟨t, n, f, _, hM⟩ := h
  exact lieModel_catalog G t n 3 f hM

theorem catalog_of_chev3_or_psl_four_four {G : Type} [Group G]
    (h : Chev3 G ∨ LieModel G .PSL 4 2 2) : Catalog G := by
  rcases h with h | h
  · exact catalog_of_chev3 h
  · exact lieModel_catalog G .PSL 4 2 2 h

theorem smallF3OmegaAsc_of_aschMainTheorem (h : AschMainTheorem) : SmallF3OmegaAsc := by
  intro G _ _ L hL hcat hQ hA2
  have hsimple := hL.simple
  have hA1 := aschA1_of_smallF3Cyclic hL
  have hmain := h G hsimple hL.kProper hcat hA1 hA2
    ⟨L, inF_of_smallF3Cyclic hL hQ, inC_of_smallF3Cyclic hL⟩
  exact hcat (catalog_of_chev3_or_psl_four_four hmain)

end CFSG.OddStandard.SmallF3.Omega
