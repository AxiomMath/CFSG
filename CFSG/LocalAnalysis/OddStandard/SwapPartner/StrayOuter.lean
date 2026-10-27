module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayOuterDihedral
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayInner
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayOuterShape
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayQuaternion
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayPerfect

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup CFSG.ComponentClassification.AschbacherKnownGroup

theorem four_le_card_inf_centralizer_of_simple (hF : DihedralOuterInvolutionFact) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hL : IsSimpleGroup ↥L)
    (hnab : ∃ x y : L, x * y ≠ y * x) {a : G} (ha : a ^ 2 = 1)
    (haN : a ∈ normalizer (L : Set G)) :
    4 ≤ Nat.card ↥(L ⊓ centralizer ({a} : Set G)) := by
  by_cases haL : a ∈ L
  · exact four_le_card_inf_centralizer_of_mem hL hnab haL ha
  · by_contra hlt
    push Not at hlt
    have hle : Nat.card ↥(L ⊓ centralizer ({a} : Set G)) ≤ 3 := by omega
    haveI : IsSimpleGroup ↥L := hL
    haveI : Group.IsPerfect ↥L :=
      CFSG.TwoRankLowerBound.Helpers.perfect_of_nonabelian_simple ↥L hnab
    haveI : Nontrivial ↥L := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      haveI := hsub
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (Subsingleton.elim (x * y) (y * x))
    have h4L : 4 ∣ Nat.card ↥L := four_dvd_card_of_isPerfect
    have h2L : 2 ∣ Nat.card ↥L := dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4L
    obtain ⟨T, hT | ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩⟩ :=
      exists_sylow_shape_of_small_centralizer ha haN haL h2L hle
    · exact (CFSG.TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_nonabelian_simple
        ↥L hnab (even_iff_two_dvd.mpr h2L) T) hT
    · exact false_of_dihedral_small_centralizer hF hL hnab h2L
        (show HasDihedralSylowTwo ↥L from by
          refine ⟨T, m + 1, by omega, ?_⟩
          rw [Nat.add_sub_cancel]
          exact ⟨e⟩)
        ha haN haL hle
    · exact false_of_quaternion_sylow_of_simple hL hnab T hn ⟨e⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
