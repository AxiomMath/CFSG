module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallAlphaThree
public import CFSG.LocalAnalysis.AGLEmbedding.J3Facts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveModels
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCatalog
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint

theorem kFactJ3Involve_of
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hbr : Nonempty (NativeSporadic.Carrier .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group))
    (hOR : KFactJ3OuterRank) : KFactJ3Involve := by
  intro KC _ _ ⟨eKC⟩ L _ _ hs hnab hcat TL hTL _ hrank A f hf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ3card : Nat.card (TauCeti.CFSGIndex.sporadic .J3).Group = 50232960 := by
    obtain ⟨b⟩ := hbr
    rw [← Nat.card_congr b.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  have hdvd : Nat.card L ∣ 50232960 := hJ3card ▸ card_dvd_of_central_extension hnab eKC A f hf
  have hC : Catalog L := hbridge L hnab hcat
  rcases j3_catalog_cases hC hnab hdvd with h | h | h | ⟨h, K, _, _, hK, ⟨θ⟩⟩ |
      ⟨h, K, _, _, hK, ⟨θ⟩⟩ | ⟨K, _, _, hK, ⟨θ⟩⟩ | hJ
  ·
    exact h
  ·
    exfalso
    exact hTL (isCyclic_sylow_three_of_card_three (m := 20) (by rw [h]) (by norm_num) TL)
  ·
    exfalso
    exact hTL (isCyclic_sylow_three_of_card_three (m := 1360) (by rw [h]) (by norm_num) TL)
  ·
    exfalso
    obtain ⟨g, hg⟩ := exists_orderOf_nine_psl_seventeen hK
    exact hTL (isCyclic_sylow_three_of_orderOf_nine (m := 272) (by rw [h]) (by norm_num)
      (by rw [MulEquiv.orderOf_eq, hg] : orderOf (θ.symm g) = 9) TL)
  ·
    exfalso
    obtain ⟨g, hg⟩ := exists_orderOf_nine_psl_nineteen hK
    exact hTL (isCyclic_sylow_three_of_orderOf_nine (m := 380) (by rw [h]) (by norm_num)
      (by rw [MulEquiv.orderOf_eq, hg] : orderOf (θ.symm g) = 9) TL)
  ·
    exfalso
    have h3 := three_le_pRank_of_psu_four_two hK θ
    have := pRank_le_pRank_mulAut_of_nonabelian hnab (by norm_num) h3
    omega
  ·
    exfalso
    obtain ⟨b⟩ := hbr
    obtain ⟨e⟩ := hJ
    have := (hOR L ⟨e.trans b⟩).2
    have h3 := pRank_le_pRank_mulAut_of_nonabelian hnab (by norm_num) this.ge
    omega

end CFSG.AGLEmbedding
