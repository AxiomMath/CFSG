module

public import CFSG.LocalAnalysis.EvenBN.G2.QMain
public import CFSG.LocalAnalysis.EvenBN.G2.QFactsFour
public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourCat
public import CFSG.LocalAnalysis.EvenBN.G2.ProductComplementFour
public import CFSG.Yardstones.M41b0c98b3153.Definitions

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (xor_of_exactClosure)


namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {K : Type} [Field K]
  [Finite K] [CharP K 2]

theorem false_of_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4) : False := by
  have hQ := h.qFacts_four d hK hK4 slmCatalogueClausesAt_three_G2
  obtain ⟨hsyl₂, -, α₂, hex₂⟩ := h.yamada_5_59_N₂ hW d hK hQ
  rcases xor_of_exactClosure hex₂ with ⟨hPa, -⟩ | ⟨hFa, -⟩
  · exact h.false_of_qFacts hW d hK hQ (h.exists_complement₂_four hW d hK hQ hK4 hsyl₂ hex₂ hPa)
  · exact h.false_of_fieldCase hW d hK hQ hsyl₂ hex₂ hFa

end Setup

theorem g2FourCenterlessExclusion_holds :
    CFSG.Yardstones.M41b0c98b3153.G2FourCenterlessExclusion := by
  intro G _ _ _ hnonab hK L hL hZ hcore hcyc hm
  have hW : CFSG.Walter.WalterOrderForm := fun G _ _ _ hnonab P hP =>
    CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple G hnonab P hP
  obtain ⟨t, h⟩ := exists_setup hnonab hK hL hZ hcore hcyc le_rfl hm
  obtain ⟨K, _, _, _, hKc, ⟨d⟩⟩ := h.exists_data
  exact h.false_of_four hW d hKc (by rw [hKc]; norm_num)

end CFSG.LocalAnalysis.EvenBN.G2
