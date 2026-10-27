module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVCoverParts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableV_cover [Finite G] (hI : TwoHSInterface) {a z : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) (hT3 : Vert TableIIIFacts a z)
    (hT4 : Vert TableIVFacts a z) {c : G} (hc : c ∈ tab5Base a) : ∃ i, c ∈ tab5Set a z i := by
  obtain ⟨hca, m, hm⟩ := hc
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hc2 : c ^ 2 = 1 := by rw [← perp_orderOf_of_isConj_a h hca]; exact pow_orderOf_eq_one c
  have hpos : 0 < orderOf (a * c) := orderOf_pos _
  have hm' : orderOf (a * c) = 2 * m := by omega
  by_cases hm1 : m = 1
  · subst hm1
    rcases tableV_cover_two h hF1 hF2 hca hm' with h2A | h2B
    · exact ⟨0, h2A⟩
    · exact ⟨1, h2B⟩
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨hax, hcx, hax', hcx'⟩ := tableV_dihedral ha2 hc2 hca hm'
    have hmul : m * 2 = orderOf (a * c) := by omega
    have hx2 : ((a * c) ^ m) ^ 2 = 1 := by
      rw [← pow_mul, hmul]; exact pow_orderOf_eq_one _
    have hx1 : (a * c) ^ m ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    rcases isConj_of_commute hF1 hF2 (IsConj.refl a) hax.symm hx2 hx1 with hxa | hxz
    · rcases tableV_cover_four_B_six hI h hT4.self hca hm' hm2 rfl hxa hax' hcx hcx' with
        h4B | h6A
      · exact ⟨3, h4B⟩
      · exact ⟨4, h6A⟩
    · exact ⟨2, tableV_cover_four_A hI h hF1 hT3 hca (by omega) hxz hax hax' hcx hcx'⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
