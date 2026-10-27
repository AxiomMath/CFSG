module

public import Certificates.Data.Kernel.SporSch.Co1Heis
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound
public import CFSG.Certificates.Kernel.SporSch.Co1SplitSound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1DispBCCheck

public section

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.Co1Schreier.Native CFSG.KS.Raw CFSG.Sporadic.Co1.InvNative
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem decLetter_encLetterK (j : Int) : decLetter (encLetterK j) = j := by
  cases j with
  | ofNat n =>
    have e : encLetterK (Int.ofNat n) = n + n := rfl
    rw [e]
    unfold decLetter
    rw [if_pos (by omega), Int.ofNat_eq_natCast]
    omega
  | negSucc n =>
    have e : encLetterK (Int.negSucc n) = (n + 1) + (n + 1) + 1 := rfl
    rw [e]
    unfold decLetter
    rw [if_neg (by omega), Int.negSucc_eq]
    omega

theorem decWord_encWordK (w : List Int) : decWord (encWordK w) = w := by
  unfold decWord encWordK
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun j _ => decLetter_encLetterK j

theorem decWords_encWordK (ws : List (List Int)) : (ws.map encWordK).map decWord = ws := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ws]
  exact List.map_congr_left fun w _ => decWord_encWordK w

theorem validRows_unpack' (X : Nat) : validRows (unpack 24 24 X) = true := by
  rw [← unpackR_eq_unpack]
  exact CFSG.KC.Co1F2.validRows_unpackR X

theorem unpack_powWM (X : Nat) : ∀ e, unpack 24 24 (powWM X e) = pow (unpack 24 24 X) e
  | 0 => MatL.unpack_idM
  | e + 1 => by
    change unpack 24 24 (CFSG.KC.Enum.strictN (powWM X e) (fun Y => CFSG.KC.Co1B.mulWK Y X)) =
      mul (pow (unpack 24 24 X) e) (unpack 24 24 X)
    rw [MatL.strictN_eq, ← mul_unpackW, unpack_powWM X e]

theorem ne_one_of_K {W : Nat} (h : Bool.rec (motive := fun _ => Bool) true false (Nat.beq W idM) = true)
    (hs : Nat.beq (Nat.shiftRight W 576) 0 = true) : (unpack 24 24 W != one ()) = true :=
  unpack_ne_one hs h

theorem beq_of_K {X Y : Nat} (h : Nat.beq X Y = true) : (unpack 24 24 X == unpack 24 24 Y) = true := by
  rw [Nat.eq_of_beq_eq_true h]
  exact beq_self_eq_true _

theorem getD_range_unpack {F : Nat → Nat} {N i : Nat} (hi : i < N) :
    ((List.range N).map fun k => unpack 24 24 (F k)).getD i (one ()) = unpack 24 24 (F i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem heisK_sound {T X XI Y YI : Nat} (h : heisK T X XI Y YI = true) :
    heisInvCheck (unpack 24 24 T) (unpack 24 24 X) (unpack 24 24 Y) = true := by
  unfold heisK at h
  rw [MatL.strictB_eq] at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hX, hY, hX5, hY5, hW5, hWs, hW, hXW, hYW, hT, hTX⟩ := h
  have iX := (invOKW_sound hX).2
  have iY := (invOKW_sound hY).2
  have hW1 : (unpack 24 24 (CFSG.KC.Co1B.mulWK (CFSG.KC.Co1B.mulWK (CFSG.KC.Co1B.mulWK XI YI) X) Y)
      != unpack 24 24 idM) = true := by
    rw [MatL.unpack_idM]
    exact ne_one_of_K hW hWs
  unfold heisInvCheck
  simp only [iX, iY, mul_unpackW, ← unpack_powWM, ← MatL.unpack_idM, validRows_unpack',
    beq_of_K hX, beq_of_K hY, beq_of_K hX5, beq_of_K hY5, beq_of_K hW5, hW1, beq_of_K hXW,
    beq_of_K hYW, beq_of_K hT, beq_of_K hTX, Bool.and_self]

theorem dihK_sound {T C CI : Nat} (h : dihK T C CI = true) :
    (mul (unpack 24 24 C) (inv (unpack 24 24 C)) == one ()) = true ∧
      (pow (mul (unpack 24 24 T) (mul (unpack 24 24 C) (mul (unpack 24 24 T)
        (inv (unpack 24 24 C))))) 13 == one ()) = true ∧
      (mul (unpack 24 24 T) (mul (unpack 24 24 C) (mul (unpack 24 24 T)
        (inv (unpack 24 24 C)))) != one ()) = true ∧
      validRows (mul (unpack 24 24 T) (mul (unpack 24 24 C) (mul (unpack 24 24 T)
        (inv (unpack 24 24 C))))) = true := by
  unfold dihK at h
  rw [MatL.strictB_eq] at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hC, hP, hPs, hne⟩ := h
  have iC := (invOKW_sound hC).2
  have hP1 : (unpack 24 24 (CFSG.KC.Co1B.mulWK T (CFSG.KC.Co1B.mulWK C (CFSG.KC.Co1B.mulWK T CI)))
      != unpack 24 24 idM) = true := by
    rw [MatL.unpack_idM]
    exact ne_one_of_K hne hPs
  simp only [iC, mul_unpackW, ← unpack_powWM, ← MatL.unpack_idM, validRows_unpack', beq_of_K hC,
    beq_of_K hP, hP1, and_self]

end CFSG.KS.SporSch.M24

end
