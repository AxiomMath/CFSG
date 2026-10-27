module

public import Certificates.Data.Kernel.Co2CenLook
public import CFSG.Certificates.Kernel.Co2Cen.Sound

public section

namespace CFSG.KC.Co2Cen

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2J
  CFSG.KC.TabMatGrp CFSG.KLie.CT CFSG.KC.M1F2

theorem lookC_spec {CF : Nat → Nat → Nat} {NC : Nat → Nat} {X r cls : Nat}
    (h : lookC CF NC X r cls = true) :
    cls.testBit (Nat.land r 15) = true ∧ Nat.shiftRight r 4 < NC (Nat.land r 15) ∧
      elemAt (CF (Nat.land r 15)) (Nat.shiftRight r 4) = X := by
  unfold lookC at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  exact ⟨by rw [← bit_eq]; exact h.1, blt_iff.1 h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem lt_ten_of_testBit {cls c : Nat} (hcls : cls < 1024) (h : cls.testBit c = true) : c < 10 := by
  by_contra hc
  have h2 : cls < 2 ^ c := lt_of_lt_of_le hcls
    (by calc 1024 = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.testBit_eq_false_of_lt h2] at h
  exact Bool.false_ne_true h

end CFSG.KC.Co2Cen

end
