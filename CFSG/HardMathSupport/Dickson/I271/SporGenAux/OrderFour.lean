module

public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Monster.B.Mathieu.SylowSound

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Native

@[expose] def orderFourOK (n : ℕ) (t : Array ℕ) : Bool :=
  validA n t && eqA n (powArr n t 4) (idA n) && !(eqA n (powArr n t 2) (idA n))

theorem orderOf_permOfArr_of_orderFourOK {n : ℕ} {t : Array ℕ} (h : orderFourOK n t = true) :
    orderOf (permOfArr n t) = 4 := by
  simp only [orderFourOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hv, h4⟩, h2⟩ := h
  have hrep := rep_of_validA hv
  have e4 : permOfArr n t ^ 4 = 1 := (eqA_iff (rep_powArr hrep 4) rep_idA).1 h4
  have e2 : permOfArr n t ^ 2 ≠ 1 := fun e => by
    have := (eqA_iff (rep_powArr hrep 2) rep_idA).2 e
    rw [h2] at this
    exact Bool.false_ne_true this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := permOfArr n t) (by simpa using e2)
    (by simpa using e4)
  simpa using this

end CFSG.HardMathSupport.Dickson.I271
