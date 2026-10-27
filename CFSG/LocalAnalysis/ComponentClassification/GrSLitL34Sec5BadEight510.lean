module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5PumpOdd510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs217
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsBadEight

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem l34Lemma510OTwoBoundStep_of_badEight
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hMax : MaximalTwoComponentInput) (hComp : L34Cor217ComponentStep)
    (hBad : L34Lemma510BadEightStep) : L34Lemma510OTwoBoundStep := by
  intro G _ _ L t S T hset u hu huc hmax K₁ hK₁u hK₁p hK₁n htype₁ hO S₁ hS₁ hSS₁ b hb hbo hbc
    hPb hW v₀ hv₀ hK₁v₀ hfam hsup hne h1 h2 h3
  exfalso
  obtain ⟨v, hvo, hK₁v, hvbad, F, hF, hFK, hFv⟩ := hBad G L t S T hset u hu huc hmax K₁ hK₁u
    hK₁p hK₁n htype₁ hO S₁ hS₁ hSS₁ b hb hbo hbc hPb hW v₀ hv₀ hK₁v₀ hfam hsup hne h1 h2 h3
  have hbase := hset.1
  have hset' := hset
  obtain ⟨-, -, -, -, htS, -, -⟩ := hset'
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have hmax₁ := hComp G L t S T hset u huS₀ hu2 K₁ hK₁u hK₁p hK₁n htype₁
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts hbase
  have : IsSimpleGroup G := hbase.1
  have h3' := three_le_pRank_of_l34 htype₁
  have hT91 := (hMax G hsF hnF hoF hbase.2.2.1 K₁ hmax₁ (by omega)
    (Sol78.not_psp4_of_l34 htype₁) (Or.inl ⟨htype₁, hbase⟩) v hvo hK₁v).1
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hbo
  have hK₁b := le_centralizer_of_mem_zStarIn hK₁u hK₁p hO (mem_inf.mp hb).2
  have hbv : b * v = v * b :=
    mem_centralizer_singleton_iff.mp (hK₁v ((map_subtype_le _ : zStarIn K₁ ≤ K₁) (mem_inf.mp hb).2))
  have hK₁bp := isPComponent_of_pumpUp_eq hS hK hu2 hbo (hbc u (hSS₁ huS))
    (not_mem_center_of_ne_one hnonab hb1) hK₁u hK₁p hK₁b hPb
  exact hvbad (oddIn_pumpUp_le_center_of_wGroup hS hU hheld hset.1 hbo hK₁b hK₁bp hvo hbv
    hK₁v hT91 hF (hW F (hFK.trans le_sup_right) hF) hFK hFv)

end CFSG.ComponentClassification.GrSLit.GrS5
