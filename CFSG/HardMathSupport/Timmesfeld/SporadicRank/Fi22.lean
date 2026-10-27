module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.RankBound
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.Bridge.Fi22Surj
public import Certificates.Certificate9595

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.Blueprint CFSG.AGLEmbedding.R3.AlphaFi22

theorem sylowData_Fi22 :
    SylowModuleData NativeSporadic.Fi22 3 5
      ((fi22Mod.acts.filter fun g => fi22Tops.any (·.reg == g.reg)).map (·.mat)) := by
  have hN : Nat.card NativeSporadic.Fi22 = 64561751654400 := CFSG.Sporadic.Fi22.card_Fi22
  have : Finite NativeSporadic.Fi22 := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact sylowData_of_modCheckE (spec3 77) Nat.prime_three hN
    (by show 3 ^ 9 ∣ 64561751654400 ∧ ¬ 3 ^ 10 ∣ 64561751654400; norm_num)
    (by show 3 ^ 9 ≤ 81 * 3 ^ 5; norm_num) Certificates.certificate9595

theorem pRank_Fi22_le :
    CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.Fi22) ≤ 7 := by
  have hN : Nat.card NativeSporadic.Fi22 = 64561751654400 := CFSG.Sporadic.Fi22.card_Fi22
  have : Finite NativeSporadic.Fi22 := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  refine pRank_le_of_sylowModuleData (X := NativeSporadic.Fi22) (n := 5) (t := 4) (z := 3)
    Nat.prime_three sylowData_Fi22 ?_ ?_ ?_
  · rw [hN]
    exact factorization_eq_of_pow_dvd Nat.prime_three (by norm_num)
      (by show 3 ^ 9 ∣ 64561751654400 ∧ ¬ 3 ^ 10 ∣ 64561751654400; norm_num)
  · rw [Nat.card_eq_fintype_card]
    decide +kernel
  · intro a j ha hj h1 h2
    omega

theorem bigCoverRankAt_Fi22 :
    BigCoverRankAt .Fi22 := by
  have hN : Nat.card NativeSporadic.Fi22 = 64561751654400 := CFSG.Sporadic.Fi22.card_Fi22
  have : Finite NativeSporadic.Fi22 := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  obtain ⟨D, P, hn, hA, hF, -⟩ := sylowData_Fi22
  have hb : Nonempty (NativeSporadic.Fi22 ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) :=
    CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have hup := pRank_Fi22_le
  have hup' : CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.Fi22) ≤ D.n + 2 := by
    rw [hn]; exact hup
  refine bigCoverRankAt_of_data (s := .Fi22) (X := NativeSporadic.Fi22) ?_ ?_ ?_ ?_ ?_
  · exact hb
  · exact D
  · exact hA
  · exact hF
  · exact hup'

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
