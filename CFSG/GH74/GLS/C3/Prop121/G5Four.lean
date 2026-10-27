module

public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions
public import CFSG.GH74.GLS.C3.Layer3.Basic

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm CFSG.GH74.GLS.Layer3 CFSG.GH74.GLS.C3.Layer2

theorem numMoved_eq_four_of_card_centralizer (u : alternatingGroup (Fin 9)) (hu : orderOf u = 2)
    (hc : Nat.card ↥(Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 9)))) = 480) :
    numMoved (u : Perm (Fin 9)) = 4 := by
  rcases numMoved_eq_of_involution_alternating 9 (by norm_num) u hu with h | h
  · exact h
  · exfalso
    have h8 : 8 ≤ 9 := by norm_num
    have hY : numMoved ((altY h8 : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 8 := by
      show (yPerm h8).support.card = 8
      rw [← Equiv.Perm.sum_cycleType, yPerm_cycleType]
      rfl
    have hconj : IsConj u (altY h8) :=
      isConj_alternating_of_numMoved_eq 9 u (altY h8) hu (orderOf_altY h8) (by rw [h, hY])
    have h1 := card_centralizer_eq_of_isConj hconj
    have h2 := card_centralizer_altY h8
    rw [hc] at h1
    simp at h2
    omega

end CFSG.GH74.GLS.C3.Prop121
