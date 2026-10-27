module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.M7Frame

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem m7Facts : Certificates.S3x3GL42.Facts :=
  Certificates.certificate320040

theorem leafM7 [DSLeaf LeafFrattiniFaithful] [DSLeaf LeafRankBounds] :
    LeafM7 := by
  intro G _ _ L P d k h hk hko
  obtain ⟨t, hC⟩ := M7.exists_ctx h hk hko
  have hQ : IsPGroup 2 (pCoreOf 2 P) :=
    CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 P
  have hPQ : P ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P
  have hPΦ : P ≤ Subgroup.normalizer ((dsFrattini (pCoreOf 2 P) : Subgroup G) : Set G) :=
    fun g hg => frattiniChief_mem_normalizer _ (hPQ hg)
  have h16 := hC.relIndex_sixteen
  obtain ⟨F₀⟩ := exists_elemFrame (frattiniChief_isElemSec _ hQ) h16 hPQ hPΦ
  obtain ⟨F, hker, hstd⟩ := hC.exists_std_frame F₀ (hC.frame_ker F₀)
  have hrel := hC.rel_mat F hker
  refine ⟨h16, ?_⟩
  rcases hstd with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · rw [hA, hB] at hrel
    obtain ⟨hcent, hI⟩ := m7Facts.stdI _ hrel
    exact ⟨hC.relIndex_dvd_six F hker (by rw [hA, hB]; exact hcent),
      Or.inr (hC.type1_of_frame F hker hA hB hcent hI)⟩
  · rw [hA, hB] at hrel
    obtain ⟨hcent, hII⟩ := m7Facts.stdII _ hrel
    exact ⟨hC.relIndex_dvd_six F hker (by rw [hA, hB]; exact hcent),
      Or.inl (hC.type2_of_frame F hA hB hII)⟩

end CFSG.GH74.QTGen4.DSGen4
