module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem gzNo_not_isConj {a z : G} (h : IsF5Type a z) (hOrb : GzOrbitFacts a z) :
    ¬ IsConj a z := by
  intro hc
  have hz2 : z ^ 2 = 1 := by rw [← h.orderOf_z]; exact pow_orderOf_eq_one z
  have h1 : Nat.card ↥(Gx z ⊓ Gx z) = 2 ^ 11 * 15 := hOrb.orbit_QA.2 z ⟨self_mem_Qz hz2, hc⟩
  rw [inf_idem] at h1
  have h2 : (2 : ℕ) ^ 11 * 15 = 2 ^ 9 * 7200 := h1.symm.trans (card_centralizer_z_of_isF5Type h)
  norm_num at h2

theorem gzNo_card_le_of_le_Qz (hC : CSideFacts) {a w : G} (h : IsF5Type a w) {E : Subgroup G}
    (hE : E ≤ Qz w) (hEl : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ 5 := by
  have hQ := isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  have hEle : E ≤ Gx w := hE.trans (Subgroup.map_subtype_le _)
  have hE'Q : E.subgroupOf (Gx w) ≤ CFSG.pCore 2 ↥(Gx w) := by
    intro c hc
    obtain ⟨q, hq, hqc⟩ := Subgroup.mem_map.mp (hE (Subgroup.mem_subgroupOf.mp hc))
    have hqc' : q = c := Subtype.ext hqc
    rw [← hqc']
    exact hq
  have hE'el : CFSG.Open.IsElemAbelian 2 (E.subgroupOf (Gx w)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun c hc => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have h1 := hEl.1.is_comm.comm (⟨((a : ↥(Gx w)) : G), Subgroup.mem_subgroupOf.mp a.2⟩ : ↥E)
        ⟨((b : ↥(Gx w)) : G), Subgroup.mem_subgroupOf.mp b.2⟩
      have h2 := congrArg Subtype.val h1
      exact h2
    · apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hEl.2 _ (Subgroup.mem_subgroupOf.mp hc)
  have hcard : Nat.card ↥(E.subgroupOf (Gx w)) = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv
  rw [← hcard]
  exact hC.rank_two ↥(Gx w) (CFSG.pCore 2 ↥(Gx w)) hQ _ hE'Q hE'el

end CFSG.EvenSporadicStandard.HNRecog.Section3
