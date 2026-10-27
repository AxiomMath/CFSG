module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs217
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open Subgroup

theorem l34Sec5ComponentInvariantStep_of_comp
    (hMax : MaximalTwoComponentInput) (hComp : L34Cor217ComponentStep) :
    L34Sec5ComponentInvariantStep := by
  intro G _ _ L t S T hset u hu hu2 K₁ hK₁u hK₁p hK₁n htype₁
  have hmax₁ := hComp G L t S T hset u hu hu2 K₁ hK₁u hK₁p hK₁n htype₁
  have hbase := hset.1
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts hbase
  have : IsSimpleGroup G := hbase.1
  have h3 := three_le_pRank_of_l34 htype₁
  have hT92 := (hMax G hsF hnF hoF hbase.2.2.1 K₁ hmax₁ (by omega)
    (Sol78.not_psp4_of_l34 htype₁) (Or.inl ⟨htype₁, hbase⟩) u hu2 hK₁u).2 h3
  have hCN₁ := centralizer_le_normalizer_of_isPComponent hT92 hK₁u hK₁p
  exact fun s hs => hCN₁ (mem_inf.mp hs).2

end CFSG.ComponentClassification.GrSLit.GrS5
