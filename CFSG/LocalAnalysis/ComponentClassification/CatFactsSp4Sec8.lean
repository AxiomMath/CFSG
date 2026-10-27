module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4q

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open CFSG.ComponentClassification.GSThmB

theorem cfSec8JOrder : CFSec8JOrder := by
  intro Y₀ _ _ p f hp hp2 hf hY
  rcases hY with h | ⟨rfl, rfl, ⟨e⟩⟩
  · exact card_of_lieModel_psl_sq hp2 h
  · rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]
    rfl

theorem cfSec8Order : CFSec8Order := by
  intro K₀ _ _ Y₀ _ _ p f hp hp2 hf h5 hK hY
  rcases hK with hK | ⟨rfl, rfl, -⟩
  · rcases hY with hY | ⟨rfl, rfl, -⟩
    · have h1 := two_mul_card_of_lieModel_psp hp2 hK
      have h2 : Nat.card Y₀ * 2 ≤ (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := by
        rw [card_of_lieModel_psl_sq hp2 hY]
        exact Nat.div_mul_le_self _ _
      have hlt := psl_sq_lt_psp (q := p ^ f) (by omega)
      omega
    · norm_num at h5
  · norm_num at h5

end CFSG.ComponentClassification.CatFactsSp4
