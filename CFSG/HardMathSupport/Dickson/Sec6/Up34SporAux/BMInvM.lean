module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvMData
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInv
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator.YS08

theorem noL3Comp_of_invertedByTwoA
    {G : Type} [Group G] (hE : MonsterExistenceStatement G) {s : G} (hs : orderOf s = 3)
    (hinv : InvertedByTwoA s) : NoL3Comp (Subgroup.centralizer ({s} : Set G)) := by
  haveI : Finite G := hE.1.1
  have hO := gLAPPrimeCoreOf_eq_bot_of_invertedByTwoA hE Nat.prime_three (by norm_num) hs hinv
  obtain ⟨α, H, hα, hαs, hH, -, hcard, hHα, hHs, hHn, hCQ⟩ := M_inverted_data hE hs hinv
  have hG : Nat.card G = CFSG.Open.monsterOrder := hE.1.2.2.2
  rw [monsterOrder_eq_numeral] at hG
  refine noL3Comp_of_inverted hα hαs hO hH hHα hHs hHn hCQ ?_ ?_
  · intro k hk
    rw [hG] at hk
    rcases hcard with h | h
    · rw [h]; exact factorial_lt_M_fi23 k hk
    · rw [h]; exact factorial_lt_M_th k hk
  · intro r ε e he hc hdvd
    rw [hG] at hdvd
    rcases hcard with h | h
    · rw [h]; exact l3_not_dvd_sq_M_fi23 r ε e he hc hdvd
    · rw [h]; exact l3_not_dvd_sq_M_th r ε e he hc hdvd

end CFSG.HardMathSupport.Dickson.Sec6.BM
