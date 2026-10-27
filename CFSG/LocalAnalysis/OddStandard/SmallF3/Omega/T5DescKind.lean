module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Kinds

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem t5_desc_kind_iff (hM : Asc82Tab6M) (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G)) (hs2 : orderOf s = 2)
    (hnc : s ∉ centralizer (L : Set G)) {k : ℕ} (hk : k < 6) :
    Kind5 L s k ↔ KindM (DescL L t) (descElt L t s hs) k := by
  interval_cases k
  ·
    have hiff := hM.inner_iff (DescG L t) (DescL L t) (t5_isOm6M_descL hL ht ht2)
      (descElt L t s hs) (t5_desc_orderOf hL ht ht2 hs hs2 hnc)
      (t5_desc_mem_normalizer L t hs)
    simp only [Kind5, KindM]
    rw [← hiff]
    constructor
    · rintro ⟨hi, hc⟩
      exact ⟨(t5_desc_innerOn_iff hL ht ht2 hs).mpr hi,
        fun hc' => hc ((t5_desc_mem_centralizer_iff hL ht ht2 hs).mp hc')⟩
    · rintro ⟨hi, hc⟩
      exact ⟨(t5_desc_innerOn_iff hL ht ht2 hs).mp hi,
        fun hc' => hc ((t5_desc_mem_centralizer_iff hL ht ht2 hs).mpr hc')⟩
  ·
    simp only [Kind5, KindM]
    exact (t5_desc_inducesTypeSome_iff hL ht ht2 hs 6 (-1) 4 (-1)).symm
  ·
    simp only [Kind5, KindM]
    exact exists_congr fun α => (t5_desc_inducesTypeSome_iff hL ht ht2 hs 6 (-1) 1 α).symm
  ·
    simp only [Kind5, KindM]
    exact exists_congr fun α => (t5_desc_inducesTypeSome_iff hL ht ht2 hs 6 (-1) 3 α).symm
  ·
    simp only [Kind5, KindM]
    exact (t5_desc_inducesProjective_iff hL ht ht2 hs 6 (-1)).symm
  ·
    simp only [Kind5, KindM]
    exact (t5_desc_inducesOutsideGStar_iff hL ht ht2 hs 6 (-1)).symm

end CFSG.OddStandard.SmallF3.Omega
