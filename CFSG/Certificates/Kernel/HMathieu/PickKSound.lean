module

public import Certificates.Data.Kernel.HMathieu.PickK

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu

theorem bif_ble (a b : Nat) : (bif Nat.ble a b then a else b) = min a b := by
  rw [Nat.min_def]
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hab => by rw [Nat.ble_eq_true_of_le hab] at h; exact absurd h (by decide)
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

theorem reduceK_eq : ∀ (bs : List Nat) (x : Nat), reduceK bs x = reduceBy bs x
  | [], _ => rfl
  | b :: bs, x => by
    have e : reduceK (b :: bs) x = reduceK bs (bif Nat.ble x (Nat.xor x b) then x else Nat.xor x b) :=
      rfl
    rw [e, bif_ble, reduceK_eq bs, reduceBy, reduceBy, List.foldl_cons]
    rfl

theorem insK_eq (r : Nat) : ∀ l : List Nat, insK r l = insertDesc r l
  | [] => rfl
  | b :: bs => by
    have e : insK r (b :: bs) = bif Nat.blt b r then r :: b :: bs else b :: insK r bs := rfl
    rw [e, insK_eq r bs, insertDesc]
    cases h : Nat.blt b r
    · have : ¬ b < r := fun hb => by
        have := Nat.blt_eq.mpr hb
        rw [h] at this
        exact Bool.false_ne_true this
      simp [this]
    · have : b < r := by simpa [Nat.blt_eq] using h
      simp [this]

theorem pickK_eq (vs : List Nat) : pickK vs = pickBasis vs := by
  unfold pickK pickBasis
  congr 1
  refine congrArg (fun f => List.foldl f ([], []) vs) (funext fun st => funext fun v => ?_)
  rw [reduceK_eq, insK_eq]
  cases h : Nat.beq (reduceBy st.1 v) 0
  · have : ¬ reduceBy st.1 v = 0 := fun e => by rw [e] at h; exact absurd h (by decide)
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem predXiKF_eq : predXiKF = predXiK := by
  funext n r fb F m L S st
  unfold predXiKF predXiK
  rw [pickK_eq]

end CFSG.KC.HMathieu

end
