module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFive
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.SectionRank Subgroup
open PGroupL515

variable {G : Type} [Group G] [Finite G]

theorem pGroupExtraspecialOmegaOne : PGroupExtraspecialOmegaOne G := by
  intro p hp _ Y C hY hY2 hCY hR2 x hx hxp
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have hYn : Y ≤ normalizer (C : Set G) :=
    (Subgroup.le_centralizer_iff.mp hCY).trans (Subgroup.centralizer_le_normalizer _)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hYn] at hx
  obtain ⟨y, hy, c, hc, rfl⟩ := hx
  have hyc : y * c = c * y := mem_centralizer_iff.mp (hCY hc) y hy
  have hcp : c ^ p = 1 := by
    rw [Commute.mul_pow hyc, hY.2.2 y hy, one_mul] at hxp
    exact hxp
  by_contra hyc'
  have hcY : c ∉ Y := fun h => hyc' (Y.mul_mem hy h)
  obtain ⟨E, hEY, hEe, hEc⟩ := exists_pRank hp1 Y
  have hF : IsElemAbelian p (E ⊔ zpowers c) :=
    hEe.sup_of_commute (isElemAbelian_zpowers hcp) fun a ha b hb =>
      mem_centralizer_iff.mp (hCY (zpowers_le.mpr hc hb)) a (hEY ha)
  have hFR : E ⊔ zpowers c ≤ Y ⊔ C :=
    sup_le (hEY.trans le_sup_left) ((zpowers_le.mpr hc).trans le_sup_right)
  have hlt : E < E ⊔ zpowers c :=
    lt_of_le_of_ne le_sup_left fun h => hcY (hEY (h ▸ (le_sup_right (a := E) (mem_zpowers c))))
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hF.isPGroup
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [hEc, hj] at hcard
  have hjk : Open.pRank p Y < j := (Nat.pow_lt_pow_iff_right hp1).mp hcard
  have := le_pRank hp1 hFR hF hj
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
