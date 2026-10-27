module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvCore
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvBData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeAssemble
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Cases

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.Sec6.BM

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem le_thirteen_of_pow_le_B {k : ℕ} (hk : 360 ^ k ≤ 4154781481226426191177580544000000) :
    k ≤ 13 := by
  by_contra h
  have h14 : 360 ^ 14 ≤ 360 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := h14.trans hk
  norm_num at this

theorem not_dvd_factorial_B_fi22 {k : ℕ} (hk : 360 ^ k ≤ 4154781481226426191177580544000000) :
    ¬ 64561751654400 ∣ k.factorial := by
  intro hd
  have h1 : 64561751654400 ≤ k.factorial := Nat.le_of_dvd (Nat.factorial_pos k) hd
  have h2 : k.factorial ≤ (13).factorial := Nat.factorial_le (le_thirteen_of_pow_le_B hk)
  have h3 : (13).factorial = 6227020800 := by decide
  omega

section Inverted


theorem false_of_isHatSix_of_inverted_B {s d : NativeSporadic.B} (hs : orderOf s = 3)
    (hd : BabyInv 0 d) (hinv : d * s * d⁻¹ = s⁻¹) {K : Subgroup NativeSporadic.B}
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({s} : Set NativeSporadic.B)))
    (h : IsHatSix ↥K) : False := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hO := gLAPPrimeCoreOf_B_eq_bot_of_inverted_by_babyInv_zero hs hd hinv
  obtain ⟨H, hH, -, hcard, hHd, hHs, hHn, hCQ⟩ := B_inverted_data hs hd hinv
  have hdd : d * d = 1 := by
    have := pow_orderOf_eq_one d
    rwa [hd.1, sq] at this
  have hG : Nat.card NativeSporadic.B = 4154781481226426191177580544000000 := by
    rw [card_nativeB, monsterBabyOrder_eq_numeral]
  have h1080 : Nat.card ↥K = 1080 := gfr2_card_isHatSix h
  have hZ3 : Nat.card ↥(Subgroup.center ↥K) = 3 := h.2.1
  have key := @false_of_inverted_component NativeSporadic.B _ _ s d hdd hinv hO
  have hnc := exists_noncomm_of_perfect_center_card_three h.1 hZ3
  have hcomp := glaPComponent_of_isComponentOf_of_core_eq_bot hO hK
  refine key hH hHd hHs hHn hCQ 360 ?_ hcomp ?_ hnc ?_
  · intro k hk hdvd
    rw [hG] at hk
    rw [hcard] at hdvd
    exact not_dvd_factorial_B_fi22 hk hdvd
  · rw [hZ3, h1080]
  · rw [hcard, h1080]
    norm_num

end Inverted

end CFSG.HardMathSupport.Solomon.Coordinator
