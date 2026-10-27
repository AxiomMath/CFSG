module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem l34Sec4Setting_of_mem_center
    (hMax : MaximalTwoComponentInput) (hbase : L34BaseSetting G)
    {u t : G} {K₁ T : Subgroup G} (hT₁ : GSUnbalancingTriple u t K₁)
    (htype₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁))
    (hmax₁ : GSWeakMaximalComponent K₁)
    (hTsyl : IsSylowTwoIn T ⊤) (huT : u ∈ T) (htT : t ∈ T) (huc : ∀ s ∈ T, s * u = u * s) :
    L34Sec4Setting G u t K₁ T := by
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts hbase
  have : IsSimpleGroup G := hbase.1
  have h3 := three_le_pRank_of_l34 htype₁
  have hT92 := (hMax G hsF hnF hoF hbase.2.2.1 K₁ hmax₁ (by omega)
    (Sol78.not_psp4_of_l34 htype₁) (Or.inl ⟨htype₁, hbase⟩) u hT₁.1 hT₁.2.2.2.1).2 h3
  have hCN₁ := centralizer_le_normalizer_of_isPComponent hT92 hT₁.2.2.2.1 hT₁.2.2.2.2.1
  have hTN : T ≤ normalizer (K₁ : Set G) := fun s hs =>
    hCN₁ (mem_centralizer_singleton_iff.mpr (huc s hs))
  exact ⟨hbase, hT₁, htype₁, hmax₁, isSylowTwoIn_of_le_of_le hTsyl hTN le_top, huT, htT⟩

end CFSG.ComponentClassification.GrSLit.GrS5
