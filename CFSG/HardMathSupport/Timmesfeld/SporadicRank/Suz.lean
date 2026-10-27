module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.SpecExtract
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.Bridge.SuzSurj
public import Certificates.Certificate9594

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.Blueprint CFSG.AGLEmbedding.R3.AlphaSuz

theorem exists_spec_Suz :
    ∃ D : ModuleSpec NativeSporadic.Suz 3, D.n = 5 ∧ D.NoAlt ∧ D.NoFun := by
  have hN : Nat.card NativeSporadic.Suz = 448345497600 := CFSG.Sporadic.Suz.card_Suz
  have : Finite NativeSporadic.Suz := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  have h := sylowData_of_modCheckE (spec3 64) Nat.prime_three hN
    (by show 3 ^ 7 ∣ 448345497600 ∧ ¬ 3 ^ 8 ∣ 448345497600; norm_num)
    (by show 3 ^ 7 ≤ 9 * 3 ^ 5; norm_num) Certificates.certificate9594
  obtain ⟨D, P, hn, hA, hF, -⟩ := h
  exact ⟨D, hn.trans (by decide), hA, hF⟩

theorem pRank_Suz_le :
    CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.Suz) ≤ 7 := by
  have hN : Nat.card NativeSporadic.Suz = 448345497600 := CFSG.Sporadic.Suz.card_Suz
  have : Finite NativeSporadic.Suz := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  refine pRank_le_of_not_dvd (G := NativeSporadic.Suz) (k := 7) Nat.prime_three ?_
  rw [hN]
  norm_num

theorem bigCoverRankAt_Suz :
    BigCoverRankAt .Suz := by
  have hN : Nat.card NativeSporadic.Suz = 448345497600 := CFSG.Sporadic.Suz.card_Suz
  have : Finite NativeSporadic.Suz := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  obtain ⟨D, hn, hA, hF⟩ := exists_spec_Suz
  have hb : Nonempty (NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group) :=
    CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have hup := pRank_Suz_le
  have hup' : CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.Suz) ≤ D.n + 2 := by
    rw [hn]; exact hup
  refine bigCoverRankAt_of_data (s := .Suz) (X := NativeSporadic.Suz) ?_ ?_ ?_ ?_ ?_
  · exact hb
  · exact D
  · exact hA
  · exact hF
  · exact hup'

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
