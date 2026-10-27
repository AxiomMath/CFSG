module

public import Certificates.Data.Kernel.Co1ClosP
public import CFSG.Certificates.Kernel.Co1Seven.CenSound

public section

namespace CFSG.KC.Co1ClosP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier.Native
  CFSG.KS.SporSch.M24

local notation "U" => unpack 24 24

theorem unpack_powLK : ∀ (es : List Nat) (x : Nat), U (powLK x es) = es.foldl pow (U x)
  | [], _ => rfl
  | e :: es, x => by
    have h : powLK x (e :: es) = strictN (powWK x e) (fun y => powLK y es) := rfl
    rw [List.foldl_cons, h, MatL.strictN_eq, unpack_powLK es, unpack_powWK]

theorem tgtPK_of {x : Nat} {es : List Nat} (h1 : U x ≠ one) (he : es.foldl pow (U x) = one) :
    tgtPK x es = true := by
  have hx : Nat.beq x idM = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact h1 ((congrArg U (Nat.eq_of_beq_eq_true h)).trans MatL.unpack_idM)
  unfold tgtPK
  rw [hx, eqU_one_of ((unpack_powLK es x).trans he)]

@[expose] noncomputable def witYP (x a ai b bi : Array Nat) (m : Nat) : Array Nat :=
  mul (mul x (mul (mul a x) ai)) (pow (mul (mul b x) bi) m)

theorem witPK_sound {P : Nat → Nat} {N p m x w : Nat} (h : witPK P N p m x w = true) :
    ∃ a ai b bi, a < N ∧ ai < N ∧ b < N ∧ bi < N ∧ mul (U (P a)) (U (P ai)) = one ∧
      mul (U (P b)) (U (P bi)) = one ∧
      witYP (U x) (U (P a)) (U (P ai)) (U (P b)) (U (P bi)) m ≠ one ∧
      pow (witYP (U x) (U (P a)) (U (P ai)) (U (P b)) (U (P bi)) m) p = one := by
  unfold witPK at h
  simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨ha, hai, hb, hbi, hia, hib, hy1, hyp⟩ := h
  have hY : U (mulWK (mulWK x (mulWK (mulWK (P (fld16 w 0)) x) (P (fld16 w 1))))
      (powWK (mulWK (mulWK (P (fld16 w 2)) x) (P (fld16 w 3))) m)) =
      witYP (U x) (U (P (fld16 w 0))) (U (P (fld16 w 1))) (U (P (fld16 w 2)))
        (U (P (fld16 w 3))) m := by
    simp only [← mul_unpackW, unpack_powWK, witYP]
  refine ⟨_, _, _, _, ha, hai, hb, hbi, ?_, ?_, ?_, ?_⟩
  · rw [mul_unpackW, Nat.eq_of_beq_eq_true hia, MatL.unpack_idM]
  · rw [mul_unpackW, Nat.eq_of_beq_eq_true hib, MatL.unpack_idM]
  · intro e
    rw [← hY] at e
    rw [eqU_one_of e] at hy1
    exact Bool.false_ne_true hy1
  · rw [← hY, ← unpack_powWK, Nat.eq_of_beq_eq_true hyp, MatL.unpack_idM]

theorem closPK_sound {P : Nat → Nat} {N : Nat} {es : List Nat} {p m : Nat} {R C W : Nat → Nat}
    (h : closPK P N es p m R C W = true) {k : Nat} (hk : k < N) (ht : tgtPK (P k) es = true) :
    ∃ r c, r < N ∧ c < N ∧ mul (U (P k)) (U (P c)) = mul (U (P c)) (U (P r)) ∧
      witPK P N p m (P r) (W r) = true := by
  unfold closPK at h
  have hall := MatL.allN_iff.1 h
  have hk' := hall k hk
  rw [MatL.strictB_eq, MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, ht] at hk'
  simp only [MatL.strictB_eq] at hk'
  obtain ⟨hA, -⟩ := hk'
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hA
  obtain ⟨hr0, hr, hc, hrr, hm⟩ := hA
  have hR := hall (R k) hr
  rw [MatL.strictB_eq, MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true] at hR
  obtain ⟨-, hW⟩ := hR
  have hrr' : R (R k) = R k := Nat.eq_of_beq_eq_true hrr
  have hcond : (Nat.beq (R (R k)) (R k) && Nat.blt 0 (R k)) = true := by
    rw [hrr', Bool.and_eq_true, Nat.blt_eq]
    exact ⟨Nat.beq_refl _, hr0⟩
  rw [MatL.bAnd_eq, hcond] at hW
  simp only at hW
  refine ⟨R k, C k, hr, hc, ?_, hW⟩
  rw [mul_unpackW, mul_unpackW, Nat.eq_of_beq_eq_true hm]

end CFSG.KC.Co1ClosP

end
