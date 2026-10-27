module

public import Certificates.Data.Kernel.SporSch.J4SPowB
public import CFSG.Certificates.Kernel.SporSch.J4SPairSound

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.Sporadic.J4Schreier CFSG.SectionRank.Native

theorem beqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
variable (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
include hK

theorem powB_enc : ∀ (f : Nat) {X : Array Nat} (e : Nat), WfN X → e < 2 ^ f →
    WfN (O.pow X e) ∧ encN (O.pow X e) = powBK c rm one f (encN X) e
  | 0, X, e, _, he => by
    obtain rfl : e = 0 := by simpa using he
    rw [Ops.pow, ite_eq_left rfl]
    exact id_enc hK
  | f + 1, X, e, hX, he => by
    rw [Ops.pow]
    by_cases h0 : e = 0
    · subst h0
      rw [ite_eq_left rfl]
      exact id_enc hK
    by_cases h1 : e = 1
    · subst h1
      rw [ite_eq_right (by decide), ite_eq_left rfl]
      exact ⟨hX, rfl⟩
    rw [ite_eq_right h0, ite_eq_right h1]
    have m := mul_enc hK hX hX
    have ih := powB_enc f (e / 2) m.1 (by rw [pow_succ] at he; omega)
    have b0 : Nat.beq e 0 = false := beqF h0
    have b1 : Nat.beq e 1 = false := beqF h1
    have ev : powBK c rm one (f + 1) (encN X) e = Bool.rec (motive := fun _ => Nat)
        (powBK c rm one f (mulJ c rm (encN X) (encN X)) (e / 2))
        (mulJ c rm (encN X) (powBK c rm one f (mulJ c rm (encN X) (encN X)) (e / 2)))
        (Nat.beq (e % 2) 1) := by
      simp only [powBK, b0, b1, strictN_eq']
      rfl
    rw [ev, ← m.2, ← ih.2]
    by_cases ho : e % 2 = 1
    · rw [ite_eq_left ho, ho]
      exact mul_enc hK hX ih.1
    · rw [ite_eq_right ho, beqF ho]
      exact ⟨ih.1, rfl⟩

theorem powBP_ok {P : Pair} {a b : Nat} (hP : PairOK P a b) (f e : Nat) (he : e < 2 ^ f) :
    PairOK (powP P e) (powBK c rm one f a e) (powBK c rm one f b e) := by
  have m1 := powB_enc hK f e hP.1.1 he
  have m2 := powB_enc hK f e hP.2.1 he
  exact ⟨⟨m1.1, m1.2.trans (by rw [hP.1.2])⟩, ⟨m2.1, m2.2.trans (by rw [hP.2.2])⟩⟩

end CFSG.KS.SporSch.J4B

end
