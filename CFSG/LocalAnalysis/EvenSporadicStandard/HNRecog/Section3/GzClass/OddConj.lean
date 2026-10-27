module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.OddIndex

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_isConj_commute_of_orderOf_two {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) {t : G} (ht : orderOf t = 2) : ∃ w : G, IsConj z w ∧ t * w = w * t := by
  have hzp : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ht]
    norm_num
  obtain ⟨S, htS⟩ := hzp.exists_le_sylow
  obtain ⟨w, hwz, hwS⟩ := exists_isConj_centerOf_sylow h.orderOf_z h.cent_z S
  refine ⟨w, hwz, ?_⟩
  have hwcenter : w ∈ centerOf (S : Subgroup G) := by
    rw [hwS]
    exact Subgroup.mem_zpowers w
  have hwc : w ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hwcenter).2
  exact Subgroup.mem_centralizer_iff.mp hwc t (htS (Subgroup.mem_zpowers t))

end CFSG.EvenSporadicStandard.HNRecog.Section3
