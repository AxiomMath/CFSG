module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.CoverRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MatOpsChecks
public import CFSG.Sporadic.Bridge.Fi24Surj
public import Certificates.Certificate13601
public import Certificates.Certificate9602

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.Blueprint CFSG.AGLEmbedding.R3.AlphaFi24

theorem sylowCover_Fi24 :
    SylowModuleCover NativeSporadic.Fi24prime 3 7 fi24Matrices := by
  have hN : Nat.card NativeSporadic.Fi24prime = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  have : Finite NativeSporadic.Fi24prime := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact sylowCover_of_modCheckV (CFSG.RankThree.Asc83Table.matOpsSpec 3 781) Nat.prime_three hN
    (by show 3 ^ 16 ∣ 1255205709190661721292800 ∧ ¬ 3 ^ 17 ∣ 1255205709190661721292800; norm_num)
    (modCheckV_matOps Certificates.certificate9602)

theorem pRank_Fi24_le :
    CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.Fi24prime) ≤ 9 := by
  have hN : Nat.card NativeSporadic.Fi24prime = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  have : Finite NativeSporadic.Fi24prime := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact pRank_le_nine_of_cover (X := NativeSporadic.Fi24prime) sylowCover_Fi24
    Certificates.certificate13601

theorem bigCoverRankAt_Fi24 :
    BigCoverRankAt .Fi24Prime := by
  have hN : Nat.card NativeSporadic.Fi24prime = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  have : Finite NativeSporadic.Fi24prime := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  obtain ⟨D, P, hn, hA, hF, -⟩ := sylowCover_Fi24
  have hb : Nonempty (NativeSporadic.Fi24prime ≃*
      (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) :=
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have hup := pRank_Fi24_le
  have hup' : CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.Fi24prime) ≤ D.n + 2 := by
    rw [hn]; exact hup
  refine bigCoverRankAt_of_data (s := .Fi24Prime) (X := NativeSporadic.Fi24prime) ?_ ?_ ?_ ?_ ?_
  · exact hb
  · exact D
  · exact hA
  · exact hF
  · exact hup'

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
