module

public import Certificates.Data.Kernel.HeE8K
public import Certificates.Data.TabMSevenHeE8
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.HeE8K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.HardMathSupport.Dickson.I271.TabMSeven

theorem unpack_rd (P q : Nat) : (unpack 8330 14 P)[q]! = rdK P q := by
  unfold rdK
  rcases Nat.lt_or_ge q 8330 with h | h
  · rw [Nat.blt_eq.mpr h, unpack, getElem!_pos _ q (by rw [Array.size_ofFn]; exact h),
      Array.getElem_ofFn]
  · have hb : Nat.blt q 8330 = false :=
      Bool.eq_false_iff.mpr fun h' => absurd (Nat.blt_eq.mp h') (by omega)
    rw [hb, getElem!_neg _ q (by rw [unpack, Array.size_ofFn]; omega)]
    rfl

theorem evPt_unpack (P0 P1 : Nat) :
    evPt (unpack 8330 14 P0) (unpack 8330 14 P1) = evK P0 P1 := by
  funext w p
  induction w with
  | nil => rfl
  | cons k w ih =>
    change (if k = 0 then (unpack 8330 14 P0)[evPt _ _ w p]! else (unpack 8330 14 P1)[evPt _ _ w p]!)
      = Bool.rec (motive := fun _ => Nat) (rdK P1 (evK P0 P1 w p)) (rdK P0 (evK P0 P1 w p))
        (Nat.beq k 0)
    rw [ih, unpack_rd, unpack_rd]
    by_cases hk : k = 0
    · rw [if_pos hk, hk]
      rfl
    · rw [if_neg hk, Bool.eq_false_iff.mpr fun h' => hk (Nat.eq_of_beq_eq_true h')]

theorem heE8OK_eq (A B : Array Nat) : heE8OK A B = heE8OKF (evPt A B) := rfl

end CFSG.KC.HeE8K
