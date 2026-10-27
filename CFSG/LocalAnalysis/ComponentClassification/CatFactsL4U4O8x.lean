module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8w
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8g
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8n

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup

theorem outerInvCentO8 : OutInv.OuterInvCentO8 := by
  intro K _ _ p e hp hp2 he hK b c hirr φ hφ2 hφout J' hJφ hJ hJm
  have hK' : Nat.card K = p ^ e := by rw [Nat.card_eq_fintype_card, hK]
  have hφ1 : φ ≠ 1 := fun h => hφout ⟨1, by rw [map_one, h]⟩
  have hQ0 := exists_ne_zero K b c hp he hK' hirr
  obtain ⟨A, μ, c₀, hsim, hsq, hμc, hns, hφ, ⟨gφ, hgφ, hgφ1, hAg⟩, hsqc, rest⟩ :=
    exists_model hp hp2 he hK' hirr hQ0 φ hφ2 hφ1 J' hJφ hJ hJm
  have : Fact (¬ IsSquare (c₀ : K)) := ⟨hsqc⟩
  obtain ⟨δ, hδ, h2, d, χ, y, hχA, hQd, hy, hJy⟩ := rest
  have hodd : Odd (Nat.card K) := by rw [hK']; exact (hp.odd_of_ne_two hp2).pow
  exact ⟨fun ψ hψφ hψJ _ => outer_cent_O8 hp hp2 he hK' hirr hQ0 φ A μ c₀ hsim hsq hμc hns gφ
      hgφ hgφ1 hAg δ h2 χ y hχA hy J' hJy ψ hψφ hψJ,
    outer_fus_O8 hirr hodd hQ0 φ A μ hsim hφ (c₀ : K) δ hδ h2 d χ y hχA hQd hy J' hJy⟩

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
