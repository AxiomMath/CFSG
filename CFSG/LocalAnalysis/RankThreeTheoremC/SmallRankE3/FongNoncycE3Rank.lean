module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Exc
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Planes
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc

open CFSG.Open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3 (KGThreeRankBig KGNoncycCentSmall
  KGNoncycCentE3)

set_option linter.unusedSectionVars false

theorem three_dvd_two_pow_sub_one {f : ℕ} (hf : Even f) : 3 ∣ 2 ^ f - 1 := by
  have h := Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.mp hf)
  have h22 : (2 : ℕ) ^ 2 - 1 = 3 := by norm_num
  rwa [h22] at h

section Big


theorem four_le_pRank_three_of_big {K : Type} [Group K] [Finite K]
    (h : catalogIs K (onLie KGThreeRankBig)) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    change KGThreeRankBig d at hi
    cases d with
    | A n q =>
      obtain ⟨hn, hp2, hf⟩ := hi
      have hmodel : StatedClassicalModel K .PSL (n + 1) q.p q.exponent :=
        CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hmodel
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) eF]
      have hF2 : Nat.card F = 2 ^ q.exponent := by rw [hF, hp2]
      refine psl_four_le_pRank_three (by omega) ?_
      rw [Nat.card_units, hF2]
      exact three_dvd_two_pow_sub_one hf
    | D n q =>
      have hp2 : q.p = 2 := hi
      obtain ⟨⟨-, -, hn4⟩, hm⟩ := CFSG.Models.lieModel_D n q hv e
      rcases hm with hm | ⟨h0, -⟩
      · obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hm
        have hF2 : Nat.card F = 2 ^ q.exponent := by rw [hF, hp2]
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hF2
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) eF]
        exact omegaPlus_four_le_pRank_three_F2 hn4
      · omega
    | twistedD n q =>
      obtain ⟨hn5, hp2⟩ := hi
      obtain ⟨⟨-, -, hn4⟩, hm⟩ := CFSG.Models.lieModel_twistedD n q hv e
      rcases hm with hm | ⟨h0, -⟩
      · obtain ⟨-, F, _, _, hF, b, c, hirr, ⟨eF⟩⟩ := hm
        have hF2 : Nat.card F = 2 ^ q.exponent := by rw [hF, hp2]
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hF2
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) eF]
        exact omegaMinus_four_le_pRank_three_F2 hn5 b c
      · omega
    | F4 q => exact four_le_pRank_three_of_exceptional q ⟨.F4 q, hv⟩ (Or.inl rfl) e
    | E6 q => exact four_le_pRank_three_of_exceptional q ⟨.E6 q, hv⟩ (Or.inr (Or.inl rfl)) e
    | E7 q =>
      exact four_le_pRank_three_of_exceptional q ⟨.E7 q, hv⟩ (Or.inr (Or.inr (Or.inl rfl))) e
    | E8 q =>
      exact four_le_pRank_three_of_exceptional q ⟨.E8 q, hv⟩ (Or.inr (Or.inr (Or.inr rfl))) e
    | twistedA _ _ => exact False.elim hi
    | B _ _ => exact False.elim hi
    | C _ _ => exact False.elim hi
    | G2 _ => exact False.elim hi
    | twistedE6 q =>
      exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.four_le_pRank_three_twistedE6 e
    | trialityD4 _ => exact False.elim hi
    | suzuki _ => exact False.elim hi
    | reeG2 _ => exact False.elim hi
    | reeF4 _ => exact False.elim hi
    | tits => exact False.elim hi

theorem kgNoncycCentE3_of_small (hS : KGNoncycCentSmall) : KGNoncycCentE3 := by
  intro K _ _ p hp hp5 hsimple hnonab hchev hK3 S B hS2 hnc hSinn hB hBS
  refine hS K p hp hp5 hsimple hnonab hchev hK3 ?_ S B hS2 hnc hSinn hB hBS
  intro hbig
  have h4 := four_le_pRank_three_of_big hbig
  omega

end Big

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc
