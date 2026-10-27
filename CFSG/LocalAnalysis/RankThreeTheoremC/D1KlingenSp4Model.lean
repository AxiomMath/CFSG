module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.KlingenSpFour

theorem prime_of_isSpFourIndex {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsSpFourIndex p d) :
    p.Prime := by
  obtain ⟨q, ⟨hqp, -, -⟩ | ⟨hp3, -, -, -⟩⟩ := hd
  · exact hqp ▸ q.prime_p
  · exact hp3 ▸ Nat.prime_three

theorem stmtKlingenModel_of (hS : KFactChevTwoSurvivorSchur) :
    StmtKlingenModel where
  center := by
    intro K _ _ p d hp2 hd hKq hZp ⟨e⟩
    rcases hd with hd | ⟨hp3, hd⟩
    · have hp : p.Prime := prime_of_isSpFourIndex hd
      have : Fact p.Prime := ⟨hp⟩
      have hmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSp 2 p 1 :=
        statedClassicalModel_of_spFourIndex d hd e
      obtain ⟨eK⟩ := nonempty_mulEquiv_psp4 hp2 hmodel
      have hperf : Group.IsPerfect K := ⟨hKq.1⟩
      have hdvd := (card_center_dvd_griess hperf eK).trans (card_griessHopf_psp4_dvd (p := p) hp2)
      obtain ⟨n, hn⟩ := hZp.exists_card_eq
      rw [hn] at hdvd
      have hn0 : n = 0 := by
        by_contra hn0
        have h1 : p ∣ 2 := (dvd_pow_self p hn0).trans hdvd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
      exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
    · subst hp3
      exact hS K 3 d (Or.inl ⟨rfl, hd⟩) hKq hZp ⟨e⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
