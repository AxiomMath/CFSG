module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeLift
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeGL
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeExtra
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeSeven
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeLinTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeUnitary
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeRee
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeM11
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

theorem glThreeAutFour {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3) : GLThreeAutFour q :=
  glThreeAutFour_of_pow_thirtySix hq3 pow_thirtySix_commute_of_normalizer

section


theorem not_surjective_of_isNineFourIndex_three {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) {i : TauCeti.CFSGIndex} (hi : IsNineFourIndex 3 i)
    (hA : ∀ (n : ℕ) (h : 5 ≤ n), i ≠ .alternating n h) {V : Type} [Group V] [Finite V]
    (hV : IsPGroup q V) (hr : CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3) (A : Subgroup (MulAut V))
    (φ : ↥A →* i.Group) : ¬ Function.Surjective φ := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hφ
  have h3 := threeAutFour_of_surjective hq2 hq3 (glThreeAutFour hq3) hV hr A φ hφ
  have h7 := sevenCentralizesTwo_of_surjective hq2 (sevenCentralizesTwoGL hq2) hV hr A φ hφ
  match i, hi, hA, h3, h7 with
  | .cyclic _ _, hi, _, _, _ => exact hi.elim
  | .alternating n h, _, hA, _, _ => exact hA n h rfl
  | .lie d, hi, _, h3, h7 =>
    rcases hi with ⟨Q, hQ, -, hd⟩ | ⟨Q, hQ, hd⟩ | ⟨-, m, hd⟩ |
      ⟨-, ⟨Q, hQ, hn, hd⟩ | ⟨Q, hQ, hn, hd⟩⟩ | ⟨h35, -⟩
    · exact not_threeAutFour_lie_A_one hd hQ h3
    · exact not_threeAutFour_lie_twistedA_two hd hQ h3
    · obtain ⟨hm, f, hf⟩ := exists_injective_psl_two_galoisField_to_ree hd
      refine not_threeAutFour_psl_two ?_ (h3.of_injective f hf)
      rw [GaloisField.card 3 (2 * m + 1) (by omega)]
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact not_sevenCentralizesTwo_lie_A_one hd hQ hn h7
    · exact kFactLThreeFourAutSection_holds q hq hq2 hq3 V hV hr A _
        ⟨d, ⟨Q, hQ, hn, hd⟩, ⟨MulEquiv.refl _⟩⟩ φ hφ
    · norm_num at h35
  | .sporadic s, hi, _, h3, _ =>
    rcases hi with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact not_threeAutFour_m11 h3
    · norm_num at h
    · norm_num at h

end

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
