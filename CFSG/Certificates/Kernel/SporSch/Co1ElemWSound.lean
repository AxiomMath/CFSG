module

public import Certificates.Data.Kernel.SporSch.Co1ElemW
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound

public section

set_option exponentiation.threshold 600

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.Co1Schreier.Native CFSG.KS.Raw CFSG.KC.Enum

theorem unpack_inj24 {X Y : Nat} (hX : X < 2 ^ 576) (hY : Y < 2 ^ 576)
    (h : unpack 24 24 X = unpack 24 24 Y) : X = Y := by
  have hr : ∀ i < 24, MatL.rowV X i = MatL.rowV Y i := fun i hi => by
    rw [← MatL.unpack_getD X i hi, ← MatL.unpack_getD Y i hi, h]
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 576
  · have key : ∀ Z : Nat, Z.testBit b = (MatL.rowV Z (b / 24)).testBit (b % 24) := by
      intro Z
      unfold MatL.rowV
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      simp only [Nat.mod_lt b (by decide : 24 > 0), decide_true, Bool.true_and]
      congr 1
      omega
    rw [key X, key Y, hr _ (by omega)]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hY (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem mulK_lt24 (X Y : Nat) : mulK X Y < 2 ^ 576 := by
  apply Nat.lt_pow_two_of_testBit
  intro t ht
  unfold mulK
  rw [MatL.foldN_eq, MatL.pack_testBit (fun i => vmulK (rowK X i) Y), List.any_eq_false]
  intro i hi
  have hi24 := List.mem_range.1 hi
  rw [MatL.testBit_false_of_lt (MatL.vmulK_lt _ _) (by omega), Bool.and_false]
  exact Bool.false_ne_true

theorem mulWK_lt24 (X Y : Nat) : CFSG.KC.Co1B.mulWK X Y < 2 ^ 576 := by
  rw [CFSG.KC.Co1B.mulWK, CFSG.KC.F2W.mulW_eq, CFSG.KC.F2W.mulF_eq_orN]
  exact CFSG.KC.F2W.orN_fields_lt fun i _ => CFSG.KC.F2W.vmF_lt _ _ _

theorem mulWK_eq_mulK : CFSG.KC.Co1B.mulWK = mulK := by
  funext X Y
  apply unpack_inj24 (mulWK_lt24 X Y) (mulK_lt24 X Y)
  rw [← mul_unpackW, MatL.unpack_mulK]

theorem powEW_eq : powEW = powK := by
  funext X e
  unfold powEW powK
  rw [mulWK_eq_mulK]

theorem eProdW_eq : eProdW = eProdK := by
  funext A n
  unfold eProdW eProdK
  rw [mulWK_eq_mulK, powEW_eq]

theorem incSlW_eq : incSlW = incSl := by
  funext A MsP lo len
  unfold incSlW incSl
  rw [eProdW_eq]

theorem eChkW_eq : eChkW = eK := by
  funext A MsP
  unfold eChkW eK
  rw [eProdW_eq]

end CFSG.KS.SporSch.M24

end
