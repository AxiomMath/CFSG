module

public import Certificates.Data.Kernel.HNLocalK
public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KS.HNLocal

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord Matrix

noncomputable abbrev OM (X : Nat) : Matrix (Fin 133) (Fin 133) (ZMod 5) := ordMat 5 133 13 1729 X

@[expose] noncomputable def cvec (x : Nat) : Fin 133 → ZMod 5 :=
  fun j => ((x / 2 ^ (3 * j.val) % 8 : Nat) : ZMod 5)

@[expose] def CCanon (x : Nat) : Prop := x < 2 ^ 399 ∧ ∀ j < 133, x / 2 ^ (3 * j) % 8 < 5

@[expose] noncomputable def nfE (PC : Nat → Nat) (n : Nat) (e : Nat → Nat) :
    Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  ((List.range' 0 n).map fun i => OM (PC i) ^ e i).prod

theorem testBit_three {x : Nat} (hx : x < 2 ^ 399) {i : Nat} (hi : 399 ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem cvec_inj {x y : Nat} (hx : CCanon x) (hy : CCanon y) (h : cvec x = cvec y) : x = y := by
  have hf : ∀ j < 133, x / 2 ^ (3 * j) % 8 = y / 2 ^ (3 * j) % 8 := by
    intro j hj
    have e := congrFun h ⟨j, hj⟩
    unfold cvec at e
    have h1 := hx.2 j hj
    have h2 := hy.2 j hj
    have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 399
  · have hj : i / 3 < 133 := by omega
    have e := hf (i / 3) hj
    have hb : ∀ z : Nat, (z / 2 ^ (3 * (i / 3)) % 8).testBit (i % 3) = z.testBit i := by
      intro z
      have h3 : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
      rw [show (8 : Nat) = 2 ^ 3 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      simp only [h3, decide_true, Bool.true_and]
      congr 1
      omega
    rw [← hb x, ← hb y, e]
  · rw [testBit_three hx.1 (by omega), testBit_three hy.1 (by omega)]

end CFSG.KS.HNLocal

end
