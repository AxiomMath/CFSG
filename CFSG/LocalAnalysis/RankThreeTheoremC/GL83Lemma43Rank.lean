module

import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l43_three_le_pRank_of_le_sup {H O E : Subgroup G} (hHO : H ≤ normalizer (O : Set G))
    (hO3 : ¬ 3 ∣ Nat.card O) (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hle : E ≤ H ⊔ O) : 3 ≤ CFSG.Open.pRank 3 H := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : 1 < (3 : ℕ) := by norm_num
  have hcard : ∀ X : Subgroup G, ¬ 3 ∣ Nat.card (O.subgroupOf X) := by
    intro X hdvd
    apply hO3
    have h1 : Nat.card (O.subgroupOf X) = Nat.card (O ⊓ X : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective X.subtype_injective]
    rw [h1] at hdvd
    exact hdvd.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hn1 : (O.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHO
  have hn2 : (O.subgroupOf (H ⊔ O)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hHO
  have h1 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(H ⊔ O)) := by
    have := hE.1
    exact CFSG.SectionRank.le_pRank_of_injective (p := 3) (k := 3) hp1
      (fun a b => mul_comm' a b)
      (fun a => Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE.2 _ a.2))
      (by rw [hE27]; norm_num) (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle) le_top
  have e : (↥H ⧸ O.subgroupOf H) ≃* (↥(H ⊔ O) ⧸ O.subgroupOf (H ⊔ O)) :=
    QuotientGroup.quotientInfEquivProdNormalizerQuotient H O hHO
  calc 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(H ⊔ O)) := h1
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup (↥(H ⊔ O) ⧸ O.subgroupOf (H ⊔ O))) :=
        (CFSG.SectionRank.pRank_quotient_eq (O.subgroupOf (H ⊔ O)) (hcard _)).symm
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup (↥H ⧸ O.subgroupOf H)) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e).symm
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) :=
        CFSG.SectionRank.pRank_quotient_eq (O.subgroupOf H) (hcard _)
    _ ≤ CFSG.Open.pRank 3 H :=
        (CFSG.SectionRank.pRank_le_map hp1 H.subtype H.subtype_injective ⊤).trans
          (CFSG.SectionRank.pRank_mono hp1 (Subgroup.map_subtype_le _))

end CFSG.LocalAnalysis.RankThreeTheoremC
