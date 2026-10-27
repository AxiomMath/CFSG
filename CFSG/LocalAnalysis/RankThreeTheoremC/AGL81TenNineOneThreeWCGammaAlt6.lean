module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaMove
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111AltSixIrred
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag

theorem kFactTenNineWCGammaAlt6 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal],
      Nonempty (K ≃* alternatingGroup (Fin 6)) →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ ⟨e⟩ S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : ∀ T : Sylow 3 K, 3 < Nat.card (T : Subgroup K) := by
    intro T
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e Hyp111.AltSixIrred.isPGroup_sylowZero
      Hyp111.AltSixIrred.not_dvd_index_sylowZero T
    rw [hΦ, Subgroup.card_map_of_injective Φ.injective, Hyp111.AltSixIrred.card_sylowZero]
    norm_num
  refine false_of_move_gamma ?_ ?_ (move_of_irred ?_ h9) S A hA3 Y hY hwc
  · intro k hk
    have hc : k ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun x => (hk x).symm
    rw [center_eq_bot_six e, Subgroup.mem_bot] at hc
    exact hc
  · rintro φ ⟨m, hm⟩
    obtain ⟨g, hg⟩ := mem_inner_of_pow_eq_one_six (X := K) e hm
    exact ⟨g, fun x => by rw [← hg, MulAut.conj_apply]⟩
  · intro T V hVT hV1 hN
    exact Hyp111.eq_of_le_sylow_of_isAltTwoP ⟨e⟩ T hVT hV1 hN

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
