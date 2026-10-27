module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofRHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofBLin
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofBSU
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.Open

theorem gl83OutDiagPowerMap_of_tables (hGA : CFSG.Open.GriessAllModelsStatement) :
    GL83OutDiagPowerMap := by
  intro p hp hp5 L _ _ hL hlin hZne hZp α δ a b hδp hδ hαδ hαc
  haveI := hL.2
  rcases hlin with ⟨n, K, _, _, hpn, hpK, ⟨e⟩⟩ | ⟨n, q, K, _, _, hKq, hpn, hpq, ⟨e⟩⟩
  · have hn5 : 5 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · haveI : Subsingleton (StatedProj (StatedSL 0 K)) := inferInstance
        exact absurd e.injective.subsingleton (not_subsingleton _)
      · exact hp5.trans (Nat.le_of_dvd hn0 hpn)
    exact outDiag_of_linear hp hp5 hGA hL hZne hZp (by omega)
      (e.trans (l212in_projectiveSLEquivStated n K).symm) α δ a b hδp hδ hαδ hαc
  · have hn5 : 5 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · haveI : Subsingleton (StatedProj (StatedSU 0 q K)) := inferInstance
        exact absurd e.injective.subsingleton (not_subsingleton _)
      · exact hp5.trans (Nat.le_of_dvd hn0 hpn)
    obtain ⟨r, m, hr, hchar, -, hKr⟩ := exists_char_pow_card K
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
      refine (Nat.dvd_prime_pow hr).1 ?_
      rw [← hKr, hKq]
      exact dvd_pow_self q two_ne_zero
    subst hqf
    exact outDiag_of_unitary hp hp5 hGA hL hZne hZp hn5 hKq e α δ a b hδp hδ hαδ hαc

theorem gl83PElementCentralizerRank_holds
    : GL83PElementCentralizerRank :=
  gl83PElementCentralizerRank_of_tables
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

theorem gl83OutDiagPowerMap_holds
    : GL83OutDiagPowerMap :=
  gl83OutDiagPowerMap_of_tables
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end CFSG.LocalAnalysis.RankFourTheoremC
