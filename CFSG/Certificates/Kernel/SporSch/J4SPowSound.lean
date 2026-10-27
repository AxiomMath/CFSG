
module

public import Certificates.Data.Kernel.SporSch.J4SPow
public import CFSG.Certificates.Kernel.SporSch.J4SColsSound

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.Sporadic.J4Schreier

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem powKF_eq : ∀ (f P m : Nat), m < 2 ^ f → powCols (unpack11 P) m = unpack11 (powKF f P m)
  | 0, P, m, hm => by
    have : m = 0 := by omega
    subst this
    rw [powCols, ite_eq_left rfl, id_eq]
    rfl
  | f + 1, P, m, hm => by
    have hd : m / 2 < 2 ^ f := by rw [pow_succ] at hm; omega
    have e : powKF (f + 1) P m = nIf(Nat.beq m 0, pidK, strictN (compK P P) (fun PP =>
        nIf(Nat.beq (m % 2) 1, compK P (powKF f PP (m / 2)), powKF f PP (m / 2)))) := rfl
    rw [e]
    by_cases h0 : m = 0
    · subst h0
      rw [powCols, ite_eq_left rfl, id_eq]
      rfl
    · rw [show Nat.beq m 0 = false from Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h),
        powCols, ite_eq_right h0, strictN_eq, comp_eq, powKF_eq f _ _ hd]
      by_cases h1 : m % 2 = 1
      · rw [ite_eq_left h1, show Nat.beq (m % 2) 1 = true by rw [h1]; rfl, comp_eq]
      · rw [ite_eq_right h1, show Nat.beq (m % 2) 1 = false from
          Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)]

end CFSG.KS.SporSch.C11

end
