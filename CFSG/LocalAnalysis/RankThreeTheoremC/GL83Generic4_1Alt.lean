module

import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen
import CFSG.RankThree.PartOne.N143.AltTwoRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThree.GroupTheory
  (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four)
open CFSG.RankThree.GroupTheory.SteinbergBY
  (high_two_rank_simple_section_small_rank_central_cover twoLocalOddRank_eq_evenRank)

theorem false_of_section_alternating {G : Type} [Group G] [Finite G]
    (he : CFSG.Open.evenRank G = 3) {n : ℕ} (hn : 13 ≤ n) {H : Subgroup G}
    (π : H →* alternatingGroup (Fin n)) (hπ : Function.Surjective π) : False := by
  have h5 : 5 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup h5
  have hnc : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
    by_contra! h
    have hc : IsMulCommutative (alternatingGroup (Fin n)) := ⟨⟨h⟩⟩
    have := alternatingGroup.isMulCommutative_iff_card_le_three.mp hc
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  obtain ⟨U, hU, hUc⟩ :=
    CFSG.RankThree.PartOne.N143.exists_isElementaryAbelian_two_pow_five (n := n) (by omega)
  have he' : CFSG.twoLocalOddRank G ≤ 3 := by
    rw [twoLocalOddRank_eq_evenRank]
    exact le_of_eq he
  obtain ⟨Y, _, _, _, φ, hφ, hφZ, hY⟩ := high_two_rank_simple_section_small_rank_central_cover
    3 he' hsimple hnc ⟨U, hU, hUc⟩ H π hπ
  let π' : (⊤ : Subgroup Y) →* alternatingGroup (Fin n) :=
    φ.comp Subgroup.topEquiv.toMonoidHom
  have hπ' : Function.Surjective π' := hφ.comp Subgroup.topEquiv.surjective
  have hZ : π'.ker ≤ Subgroup.center (⊤ : Subgroup Y) := by
    intro w hw
    have hw' : (w : Y) ∈ φ.ker := hw
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hφZ hw') (g : Y)
  have h12 := (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four
    π' hπ' hZ).2.2.1 hY
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
