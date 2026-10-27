module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvBData
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInv
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeAssemble
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Solomon.Coordinator.YS08

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Inverted


theorem noL3Comp_B_of_inverted {s d : NativeSporadic.B} (hs : orderOf s = 3) (hd : BabyInv 0 d)
    (hinv : d * s * d⁻¹ = s⁻¹) : NoL3Comp (Subgroup.centralizer ({s} : Set NativeSporadic.B)) := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hO := gLAPPrimeCoreOf_B_eq_bot_of_inverted_by_babyInv_zero hs hd hinv
  obtain ⟨H, hH, -, hcard, hHd, hHs, hHn, hCQ⟩ := B_inverted_data hs hd hinv
  have hdd : d * d = 1 := by
    have := pow_orderOf_eq_one d
    rwa [hd.1, sq] at this
  have hG : Nat.card NativeSporadic.B = 4154781481226426191177580544000000 := by
    rw [card_nativeB, monsterBabyOrder_eq_numeral]
  refine noL3Comp_of_inverted hdd hinv hO hH hHd hHs hHn hCQ ?_ ?_
  · intro k hk
    rw [hG] at hk
    rw [hcard]
    exact factorial_lt_B_fi22 k hk
  · intro r ε e he hc hdvd
    rw [hG] at hdvd
    rw [hcard]
    exact l3_not_dvd_sq_B_fi22 r ε e he hc hdvd

end Inverted

end CFSG.HardMathSupport.Dickson.Sec6.BM
