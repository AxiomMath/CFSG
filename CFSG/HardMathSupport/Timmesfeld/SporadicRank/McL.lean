module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.SpecExtract
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.Presentation.McLExact
public import Certificates.Certificate9591

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3.AlphaMcL

theorem exists_spec_McL :
    ∃ D : ModuleSpec NativeSporadic.McL 3, D.n = 4 ∧ D.NoAlt ∧ D.NoFun := by
  obtain ⟨D, hn, hA, hF⟩ := exists_spec_of_modCheck (spec3 21) Nat.prime_three
    Certificates.certificate9591
  exact ⟨D, hn.trans (by decide), hA, hF⟩

theorem pRank_McL_le :
    CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.McL) ≤ 6 := by
  have hN : Nat.card NativeSporadic.McL = 898128000 := CFSG.Sporadic.McL.card_McL
  have : Finite NativeSporadic.McL := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  refine pRank_le_of_not_dvd (G := NativeSporadic.McL) (k := 6) Nat.prime_three ?_
  rw [hN]
  norm_num

theorem bigCoverRankAt_McL :
    BigCoverRankAt .McL := by
  have hN : Nat.card NativeSporadic.McL = 898128000 := CFSG.Sporadic.McL.card_McL
  have : Finite NativeSporadic.McL := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  obtain ⟨D, hn, hA, hF⟩ := exists_spec_McL
  have hb : Nonempty (NativeSporadic.McL ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) :=
    CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have hup := pRank_McL_le
  have hup' : CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.McL) ≤ D.n + 2 := by
    rw [hn]; exact hup
  refine bigCoverRankAt_of_data (s := .McL) (X := NativeSporadic.McL) ?_ ?_ ?_ ?_ ?_
  · exact hb
  · exact D
  · exact hA
  · exact hF
  · exact hup'

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
