module

public import Certificates.Data.Kernel.GMS78RuSCent
import CFSG.Certificates.Kernel.GMS78RuSC.Basic

public section

namespace CFSG.KC.GMS.SC

open CFSG.KLie.CT CFSG.KC.Loop

private theorem land255 (x : Nat) : Nat.land x 255 = x % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 8
  simpa using this

private theorem land7 (x : Nat) : Nat.land x 7 = x % 8 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 3
  simpa using this

private theorem land3 (x : Nat) : Nat.land x 3 = x % 4 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 2
  simpa using this

private theorem shr (x k : Nat) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k

private theorem pack_eq {c T D : Nat} (hc : c < 256) (hT : T < 8) (hD : D < 8) :
    Nat.lor c (Nat.lor (Nat.shiftLeft T 8) (Nat.shiftLeft D 11)) = c + 256 * T + 2048 * D := by
  have e1 : T <<< 8 = T * 256 := Nat.shiftLeft_eq T 8
  have e2 : D <<< 11 = D * 2048 := Nat.shiftLeft_eq D 11
  have h1 : (T <<< 8 ||| c) = T * 256 + c := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega) T, e1]
  have h2 : (D <<< 11 ||| (T * 256 + c)) = D * 2048 + (T * 256 + c) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega) D, e2]
  change c ||| (T <<< 8 ||| D <<< 11) = _
  rw [Nat.or_comm (T <<< 8), ← Nat.or_assoc, Nat.or_comm c, Nat.or_assoc, Nat.or_comm c, h1, h2]
  omega

private theorem lift_pack (p : Nat) : sLift17 p =
    Nat.land p 255 + 256 * (2 * Nat.land (Nat.shiftRight p 8) 3) +
      2048 * Nat.land (Nat.shiftRight p 10) 7 := by
  unfold sLift17
  rw [pack_eq]
  · simp only [land255, land3, land7, shr, Nat.mul_eq]
  · simp only [land255]; omega
  · simp only [land3, shr, Nat.mul_eq]; omega
  · simp only [land7, shr]; omega

private theorem dec17_c (p : Nat) : Nat.land (sLift17 p) 255 = Nat.land p 255 := by
  rw [lift_pack]; simp only [land255, land3, land7, shr]; omega

private theorem dec17_t (p : Nat) :
    Nat.land (Nat.shiftRight (sLift17 p) 8) 7 = Nat.mul 2 (Nat.land (Nat.shiftRight p 8) 3) := by
  rw [lift_pack]; simp only [land255, land3, land7, shr, Nat.mul_eq]; omega

private theorem dec17_d (p : Nat) :
    Nat.land (Nat.shiftRight (sLift17 p) 11) 7 = Nat.land (Nat.shiftRight p 10) 7 := by
  rw [lift_pack]; simp only [land255, land3, land7, shr]; omega

private theorem enc17_pack {c T D : Nat} (hc : c < 256) (hT : T < 8) (hD : D < 8) :
    sEnc17 (Nat.lor c (Nat.lor (Nat.shiftLeft T 8) (Nat.shiftLeft D 11))) =
      Nat.add c (Nat.add (Nat.mul 256 (Nat.land (Nat.shiftRight T 1) 3)) (Nat.mul 1024 D)) := by
  unfold sEnc17
  rw [pack_eq hc hT hD]
  simp only [land255, land3, land7, shr, Nat.add_eq, Nat.mul_eq]
  omega

theorem mul17K_eq_row (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO p q : Nat) :
    mul17K GT DPR LIN DM DO p q =
      sMulRow LIN DM DO (sGamRow GT (Nat.land p 255)) (neGet 0 DPR (Nat.land (Nat.shiftRight p 10) 7))
        (Nat.land p 255) (Nat.mul 2 (Nat.land (Nat.shiftRight p 8) 3))
        (Nat.land (Nat.shiftRight p 10) 7) q := by
  unfold mul17K sMulK sMulRow
  simp only [dec17_c, dec17_t, dec17_d]
  rw [enc17_pack]
  · exact Nat.xor_lt_two_pow (n := 8) (by rw [land255]; omega) (by rw [land255]; omega)
  · have h11 := fget_lt (neGet 0 DPR (Nat.land (Nat.shiftRight p 10) 7)) (Nat.land q 255) 11
    refine Nat.xor_lt_two_pow (n := 3) (Nat.xor_lt_two_pow (n := 3) (Nat.xor_lt_two_pow (n := 3)
      (Nat.xor_lt_two_pow (n := 3) ?_ (fget_lt _ _ 3)) ?_) (fget_lt _ _ 3)) ?_
    · simp only [land3, shr, Nat.mul_eq]; omega
    · rw [shr _ 8]; omega
    · have := fget_lt DO (Nat.add (Nat.mul 8 (Nat.land (Nat.shiftRight p 10) 7))
        (Nat.land (Nat.shiftRight q 10) 7)) 1
      omega
  · exact fget_lt _ _ 3

theorem mul17K_mod (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO p q : Nat) :
    mul17K GT DPR LIN DM DO p q % 256 = Nat.xor (Nat.land p 255)
      (Nat.land (fget (neGet 0 DPR (Nat.land (Nat.shiftRight p 10) 7)) (Nat.land q 255) 11) 255) := by
  rw [mul17K_eq_row]
  unfold sMulRow
  dsimp only
  have h1 : Nat.xor (Nat.land p 255)
      (Nat.land (fget (neGet 0 DPR (Nat.land (Nat.shiftRight p 10) 7)) (Nat.land q 255) 11) 255) <
        256 :=
    Nat.xor_lt_two_pow (n := 8) (by rw [land255]; omega) (by rw [land255]; omega)
  have h2 := land3 (Nat.shiftRight (Nat.xor (Nat.xor (Nat.xor (Nat.xor
          (Nat.mul 2 (Nat.land (Nat.shiftRight p 8) 3))
          (fget LIN (Nat.add (Nat.mul 8 (Nat.land (Nat.shiftRight p 10) 7))
            (Nat.mul 2 (Nat.land (Nat.shiftRight q 8) 3))) 3))
          (Nat.shiftRight (fget (neGet 0 DPR (Nat.land (Nat.shiftRight p 10) 7))
            (Nat.land q 255) 11) 8))
          (fget (sGamRow GT (Nat.land p 255)) (Nat.land (fget (neGet 0 DPR
            (Nat.land (Nat.shiftRight p 10) 7)) (Nat.land q 255) 11) 255) 3))
          (fget DO (Nat.add (Nat.mul 8 (Nat.land (Nat.shiftRight p 10) 7))
            (Nat.land (Nat.shiftRight q 10) 7)) 1)) 1)
  simp only [Nat.add_eq, Nat.mul_eq] at *
  omega

theorem mul17K_div (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO p q : Nat) :
    mul17K GT DPR LIN DM DO p q / 1024 = fget DM
      (Nat.add (Nat.mul 8 (Nat.land (Nat.shiftRight p 10) 7)) (Nat.land (Nat.shiftRight q 10) 7))
      3 := by
  rw [mul17K_eq_row]
  unfold sMulRow
  dsimp only
  have key : ∀ a b D : Nat, a < 256 → b < 4 →
      (Nat.add a (Nat.add (Nat.mul 256 b) (Nat.mul 1024 D))) / 1024 = D := by
    intro a b D ha hb
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  exact key _ _ _ (Nat.xor_lt_two_pow (n := 8) (by rw [land255]; omega) (by rw [land255]; omega))
    (by rw [land3]; omega)

theorem comm_tests (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO p u : Nat)
    (h : mul17K GT DPR LIN DM DO p u = mul17K GT DPR LIN DM DO u p) :
    cDTest DM (Nat.land (Nat.shiftRight p 10) 7) (Nat.land (Nat.shiftRight u 10) 7) = true ∧
    cCTest (neGet 0 DPR (Nat.land (Nat.shiftRight p 10) 7))
      (neGet 0 DPR (Nat.land (Nat.shiftRight u 10) 7)) (Nat.land u 255) (Nat.land p 255) = true := by
  constructor
  · have := mul17K_div GT DPR LIN DM DO p u
    rw [h, mul17K_div] at this
    unfold cDTest
    rw [Nat.beq_eq]
    exact this.symm
  · have := mul17K_mod GT DPR LIN DM DO p u
    rw [h, mul17K_mod] at this
    unfold cCTest
    rw [Nat.beq_eq]
    exact this.symm

end CFSG.KC.GMS.SC

end
