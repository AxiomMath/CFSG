module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporHeis
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenTC
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBDatum

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Monster.Generated
  CFSG.RankThree.PartOne.StrongP
open scoped commutatorElement

set_option maxRecDepth 100000

theorem hasNoncommPair_three_Gmat :
    HasNoncommPair 3 Gmat :=
  hasNoncommPair_of_commData (G := Gmat) Nat.prime_three
    CFSG.AGLEmbedding.Norton.MON5_7.tbCommData (i := ⟨1, by norm_num⟩) (j := ⟨0, by norm_num⟩)
    (by rw [CFSG.AGLEmbedding.Norton.MON5_7.tbCommData.bcomm_q,
      CFSG.AGLEmbedding.Norton.MON5_7.tbM_val, pow_one])

theorem hasNoncommPair_five_Gmat :
    HasNoncommPair 5 Gmat := by
  set g : Fin 9 → Gmat :=
    fun i => CFSG.AGLEmbedding.Norton.MON5_7.gw MonsterFive.fiveGens[i.val]! with hg
  obtain ⟨hp, hc⟩ := MonsterFiveCensus.rel_of_relSet g (by
    rw [← MonsterFiveGmat.fivePw_eq, ← MonsterFiveGmat.fiveCw_eq]
    exact MonsterFive.fiveRels_holds)
  have hz1 : g 8 ≠ 1 := MonsterFive.fiveGen_eight_ne_one
  have e2 : (_root_.Timmesfeld.PcFive.pw)[(2 : Fin 9).val]! = #[0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  have e3 : (_root_.Timmesfeld.PcFive.pw)[(3 : Fin 9).val]! = #[0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  have e8 : (_root_.Timmesfeld.PcFive.pw)[(8 : Fin 9).val]! = #[0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  have c23 : (_root_.Timmesfeld.PcFive.cw)[(2 : Fin 9).val * 9 + (3 : Fin 9).val]! =
      #[0, 0, 0, 1, 0, 0, 0, 0, 3] := by decide +kernel
  have c28 : (_root_.Timmesfeld.PcFive.cw)[(2 : Fin 9).val * 9 + (8 : Fin 9).val]! =
      #[0, 0, 0, 0, 0, 0, 0, 0, 1] := by decide +kernel
  have c38 : (_root_.Timmesfeld.PcFive.cw)[(3 : Fin 9).val * 9 + (8 : Fin 9).val]! =
      #[0, 0, 0, 0, 0, 0, 0, 0, 1] := by decide +kernel
  have p2 : g 2 ^ 5 = 1 := by
    have := hp 2
    rw [e2] at this
    simpa [MonsterFiveCensus.prodAsc, List.range_succ] using this
  have p3 : g 3 ^ 5 = 1 := by
    have := hp 3
    rw [e3] at this
    simpa [MonsterFiveCensus.prodAsc, List.range_succ] using this
  have p8 : g 8 ^ 5 = 1 := by
    have := hp 8
    rw [e8] at this
    simpa [MonsterFiveCensus.prodAsc, List.range_succ] using this
  have k23 : g 2 * g 3 * (g 2)⁻¹ = g 3 * g 8 ^ 3 := by
    have := hc 2 3 (by decide)
    rw [c23] at this
    simpa [MonsterFiveCensus.prodAsc, List.range_succ] using this
  have k28 : g 2 * g 8 * (g 2)⁻¹ = g 8 := by
    have := hc 2 8 (by decide)
    rw [c28] at this
    simpa [MonsterFiveCensus.prodAsc, List.range_succ] using this
  have k38 : g 3 * g 8 * (g 3)⁻¹ = g 8 := by
    have := hc 3 8 (by decide)
    rw [c38] at this
    simpa [MonsterFiveCensus.prodAsc, List.range_succ] using this
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hz3 : g 8 ^ 3 ≠ 1 := by
    intro h
    have hord : orderOf (g 8) = 5 := orderOf_eq_prime p8 hz1
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    omega
  have c28' : Commute (g 2) (g 8) := by
    have := k28
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have c38' : Commute (g 3) (g 8) := by
    have := k38
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hcomm : ⁅g 2, g 3⁆ = g 8 ^ 3 := by
    rw [commutatorElement_def, k23, (c38'.pow_right 3).eq, mul_inv_cancel_right]
  exact CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_of_central_commutator Nat.prime_five p2 p3
    (by rw [hcomm]; exact hz3) (by rw [hcomm]; exact (c28'.pow_right 3).symm)
    (by rw [hcomm]; exact (c38'.pow_right 3).symm)

theorem hasNoncommPair_seven_Gmat :
    HasNoncommPair 7 Gmat := by
  open CFSG.AGLEmbedding.Norton.MON5_7 in
  refine ⟨xG, eG, xG_pow, eG_pow, fun h => ?_, heisS_isPGroup⟩
  open CFSG.AGLEmbedding.Norton.MON5_7 in
  have h1 : ⁅xG, eG⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
  open CFSG.AGLEmbedding.Norton.MON5_7 in
  rw [comm_xG_eG, inv_eq_one] at h1
  open CFSG.AGLEmbedding.Norton.MON5_7 in
  have h7 : zG ^ 7 = 1 := zG_pow
  open CFSG.AGLEmbedding.Norton.MON5_7 in
  have h2 : zG = 1 := by
    have h3 : orderOf zG ∣ Nat.gcd 3 7 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h7)
    rw [show Nat.gcd 3 7 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  open CFSG.AGLEmbedding.Norton.MON5_7 in
  exact zG_ne_one h2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
