module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevResStmt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevG2Rank
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.Models in
theorem lieOddRankChevG2_holds
    (hG : CFSG.Open.GriessAllModelsStatement) : LieOddRankChevG2 := by
  intro K _ _ hq Q hv hQ ⟨e⟩ r hr hr2
  haveI : Fact r.Prime := ⟨hr⟩
  have hQ3 : 3 ≤ Q.card := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hn : 2 ≤ Q.exponent := by
    by_contra h
    have h2 : Q.exponent ≤ 1 := by omega
    have : 2 ^ Q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hadm : StatedLieAdmissible .G2 0 2 Q.exponent := by
    refine ⟨Nat.prime_two, Q.exponent_pos, rfl, ?_⟩
    rw [← hQc]
    exact hQ3
  have hLM : LieModel (K ⧸ Subgroup.center K) .G2 0 2 Q.exponent :=
    ⟨hadm, Or.inr ⟨rfl, ⟨TauCeti.LieTypeIndex.G2 Q, hv⟩, ⟨hQ, rfl⟩, ⟨e⟩⟩⟩
  have hdvd := ksm_card_center_dvd hG hq hLM
  have hgen : genericOrders .G2 0 2 Q.exponent = (1, 1) := rfl
  obtain ⟨k, hk⟩ := ksm_exc_two .G2 0 Q.exponent
  rw [hgen, hk] at hdvd
  have hrZ : ¬ r ∣ Nat.card (Subgroup.center K) :=
    fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
      (hr.dvd_of_dvd_pow (h.trans (by simpa using hdvd))))
  let F := GaloisField 2 Q.exponent
  haveI : Fintype F := Fintype.ofFinite F
  have hFN : Nat.card F = 2 ^ Q.exponent := GaloisField.card 2 Q.exponent (by omega)
  have hFcard : Fintype.card F = 2 ^ Q.exponent := by rw [← Nat.card_eq_fintype_card, hFN]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 Q hv hQ F (by rw [hFN, hQc])
  have hbot : ¬ r ∣ Nat.card (Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) := by
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.card_bot]
    exact hr.not_dvd_one
  rw [← pRank_quotient_eq (Subgroup.center K) hrZ,
    pRank_top_eq_of_mulEquiv hr.one_lt (e.trans b.symm),
    pRank_quotient_eq (Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) hbot,
    pRank_adjointG2_eq F hFcard hn hr hr2, hFcard, hQc]

end CFSG.LocalAnalysis.RankThreeUC.S15
