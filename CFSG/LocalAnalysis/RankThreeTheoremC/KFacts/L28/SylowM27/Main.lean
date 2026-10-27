module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.SylowM27.OrderThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.SylowM27.Suzuki
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsL28
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.SylowM27.Focal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28

open Subgroup CFSG.ABGLocalTools CFSG.Open SylowM27


theorem kFactSylowM27_holds : KFactSylowM27 := by
  intro X _ _ K hKn hKs hKnab hKcat hKc Q hQsyl hQ hQnab ⟨a, ha, ha3⟩
  have : K.Normal := hKn
  have ha9 := orderOf_eq_nine hQ hQnab ha ha3
  obtain ⟨hcyc, hnle⟩ := isCyclic_inf_and_not_le hKs hKnab hQsyl hQ hQnab ha ha9
  refine ⟨hnle, hcyc, ?_⟩
  have hsyl : IsSylowOf 3 (Q ⊓ K) K :=
    hQsyl.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.mpr hKn).ge
  have hdvd : Nat.card ↥(Q ⊓ K) ∣ 3 ^ 3 := hQ ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exact (false_of_card_inf_eq_one hKs hKnab hKcat hKc hsyl hQ hQnab (by simpa using hk')).elim
  · exact (false_of_card_inf_eq_three hKs hKnab hsyl hQ hQnab ha ha9
      (by simpa using hk')).elim
  · exact hk'
  · exfalso
    apply hnle
    have hQK : Q ⊓ K = Q := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', hQ])
    exact hQK.ge.trans inf_le_right

end CFSG.LocalAnalysis.RankThreeTheoremC.L28
