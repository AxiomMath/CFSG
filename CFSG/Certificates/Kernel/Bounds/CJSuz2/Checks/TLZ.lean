module

public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.ConeT

public section

namespace CFSG.KD.CJSuz2T

open CFSG.KC

theorem pv_ok : ∀ d < 32, PVs d = LabZ.pwN (LabZ.pcode d) := by decide +kernel

theorem codeT_unf (i : Nat) : codeT i = Nat.land (Nat.shiftRight (LCs (Nat.shiftRight i 12))
    (Nat.mul 5 (Nat.land i 4095))) 31 :=
  LabZ.strictN_eq _ _

theorem LB_eq (i : Nat) : LB i = LabZ.pwN (LabZ.pcode (codeT i)) := by
  rw [codeT_unf]
  exact pv_ok _ (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))

theorem okL_eq (i : Nat) : okL i = okZ i := by
  unfold okL okZ
  rw [LabZ.runLab_eq LB_eq]

theorem okLM_eq (i : Nat) : okLM i = okM i := by
  unfold okLM okM
  rw [LabM.runLabM_eq LB_eq]

end CFSG.KD.CJSuz2T

end
