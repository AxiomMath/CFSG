module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCentralThreeCover
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus


theorem four_le_pRank_of_isLieOver_twistedA {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥) {r : ℕ} (hr : 4 ≤ r)
    (h : IsLieOver (↥Y ⧸ center ↥Y) (.twistedA r) 2 1) : 4 ≤ Open.pRank 3 Y := by
  classical
  obtain ⟨⟨d, hv⟩, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := h
  simp only at hd
  subst hd
  have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hqp] at hc
  obtain ⟨⟨-, -, hn3, hnq⟩, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hc
  letI : Field K := hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * q.exponent)
    (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
  have hcomp : IsComponentOf (⊤ : Subgroup ↥Y) ⊤ := isComponentOf_top_top_of_isQuasisimple hY
  have hodd : Odd (Nat.card (center ↥(⊤ : Subgroup ↥Y))) := by
    rw [card_center_top]
    exact odd_card_center_of_pCoreOf_eq_bot hO
  obtain ⟨eT⟩ := nonempty_quotient_center_top (Q := ↥Y)
  obtain ⟨ρ, -, hker, -⟩ := kFactCoverUnitary ↥Y ⊤ hcomp hodd (r + 1) (2 ^ q.exponent) K hcard
    hn3 hnq (eT.trans e')
  have h3q : 3 ∣ 2 ^ q.exponent + 1 := by
    rw [hqe]
    norm_num
  have h4 := RankOneCent.CentralThree.four_le_pRank_of_uniCover hcard (by omega) h3q ρ hker
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) Subgroup.topEquiv,
    ← CFSG.LocalAnalysis.GLTheoremB.pRank_eq_pRank_top_subtype (by norm_num) Y] at h4
  exact h4

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe
