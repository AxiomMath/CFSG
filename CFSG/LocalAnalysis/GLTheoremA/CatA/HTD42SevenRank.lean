module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bRes2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HTD42SevenGraph

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
open CFSG.Timmesfeld.ExceptionalOrders
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KFAE.OLTwisted

section TD42SevenRank


theorem td42SevenRank_holds : TD42SevenRank := by
  intro S _ _ hS E T hE hT hTne hEN
  have hmod : CFSG.Blueprint.LieModel S .trialityD4 0 2 1 :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.blueprintLieModel_td4two hS
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 2 1 := by
    rcases hmod with ⟨ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFfin, σ, hFcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two (Nat.le_refl 1) hchev.2
  have hF : Nat.card F = (2 ^ 1) ^ 3 := hFcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF3 : Fintype.card F = 2 ^ 3 := by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hF3
  haveI : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  have hH := (holds_of_chevalleyExceptionalModel hchev).of_mulEquiv e
  have hTn : ¬ 49 ∣ Nat.card (Subgroup.normalizer (T : Set S)) :=
    not_dvd_card_normalizer_of_mulEquiv (r := 49) e
      (fun U hU2 hU1 => CFSG.LocalAnalysis.GLTheoremA.HTD42Seven.not_dvd_sq_seven_card_normalizer_graphFixed_D4
        σ hF hσ hH hU1 hU2) T hT hTne
  by_contra hgt
  push Not at hgt
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hE)
  have hn2 : 2 ≤ n := by
    by_contra h2
    push Not at h2
    rw [hn] at hgt
    interval_cases n <;> norm_num at hgt
  have h49E : 49 ∣ Nat.card E := by
    rw [hn, show (49 : ℕ) = 7 ^ 2 by norm_num]
    exact pow_dvd_pow 7 hn2
  exact hTn (h49E.trans (Subgroup.card_dvd_of_le hEN))

end TD42SevenRank

end CFSG.LocalAnalysis.GLTheoremA
