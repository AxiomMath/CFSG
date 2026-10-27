module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporBasic

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Spor

open CFSG Subgroup CFSG.Blueprint

theorem fiveSpor_He :
    FiveSporClauseFor .He := by
  intro S _ _ _ hna ⟨e⟩ σ P h _ ⟨eP⟩
  obtain ⟨hσ, hPF, hP, hPne⟩ := h
  have hcardP : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 60 := by
    rw [Nat.card_congr eP.toEquiv]
    exact Even.card_alt_five (MulEquiv.refl _)
  rcases GrSLit.simpleFixedComponents_held GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
      GrSLit.HeldFix.not_isPComponent_centralizer_heT1P S
      inferInstance hna ⟨e⟩ σ hσ P hPF hP hPne with hL | hA
  · rw [CatLeaf.card_of_isL34Type hL] at hcardP
    norm_num at hcardP
  · obtain ⟨eA⟩ := hA
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcardP
    norm_num [Nat.factorial] at hcardP

end CFSG.ComponentClassification.SolMax.FiveCat.Spor
