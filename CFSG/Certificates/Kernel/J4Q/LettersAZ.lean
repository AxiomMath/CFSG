module

public import Certificates.Data.Kernel.J4Q.Words26
public import Certificates.Data.J4Ov.Fam

public section

namespace CFSG.KC.J4Q

theorem letAZ_spec (ch : Char) :
    (if 'a' ≤ ch then ((ch.toNat - 96 : Nat) : Int) else -((ch.toNat - 64 : Nat) : Int)) =
      letAZ ch.toNat := by
  have key : 'a' ≤ ch ↔ 97 ≤ ch.toNat := by
    simp only [Char.le_def, UInt32.le_iff_toNat_le]
    rfl
  unfold letAZ
  by_cases h : 97 ≤ ch.toNat
  · rw [if_pos (key.2 h), Nat.ble_eq_true_of_le h]
    rfl
  · rw [if_neg (fun h' => h (key.1 h'))]
    have hb : Nat.ble 97 ch.toNat = false := by
      cases hb : Nat.ble 97 ch.toNat
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) h
    rw [hb]
    rfl

theorem decodeWord_ofList (cs : List Char) :
    CFSG.Quasithin.J4Ov.decodeWord (String.ofList cs) = lettersAZ cs := by
  unfold CFSG.Quasithin.J4Ov.decodeWord
  rw [String.toList_ofList]
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    rw [List.map_cons, ih, letAZ_spec]
    rfl

end CFSG.KC.J4Q

end
