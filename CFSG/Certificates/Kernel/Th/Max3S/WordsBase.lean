
module

public import CFSG.Certificates.Kernel.Th.Max3S.BasicBase
public import CFSG.Certificates.Kernel.Th.Max3S.Leaves
public import CFSG.Sporadic.Th.BaseBase
public import CFSG.Sporadic.Th.ChainBase
public import CFSG.Sporadic.Th.IndexBase
public import CFSG.Sporadic.Th.Max3.AllConjBase
public import CFSG.Sporadic.Th.Max3.AllConjInputsBase
public import CFSG.Sporadic.Th.Max3.InvolutionsBase

@[expose] public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

def code : Gen → ℕ
  | .x => 0
  | .y => 1

theorem encGen_cons (g : Gen) (w : List Gen) : encGen (g :: w) = code g + 4 * encGen w := by
  cases g <;> rfl

theorem code_lt (g : Gen) : code g < 4 := by cases g <;> decide

theorem bitsN_encGen : ∀ (w : List Gen) (i : ℕ) (hi : i < w.length),
    BigS.bitsN (encGen w) (2 * i) 2 = code w[i]
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | g :: w, 0, _ => by
    rw [bitsN_eq, encGen_cons, Nat.mul_zero, Nat.shiftRight_zero]
    have := code_lt g
    simp only [List.getElem_cons_zero]
    omega
  | g :: w, i + 1, hi => by
    have hi' : i < w.length := by simpa using hi
    rw [List.getElem_cons_succ, ← bitsN_encGen w i hi', bitsN_eq, bitsN_eq, encGen_cons,
      show 2 * (i + 1) = 2 + 2 * i by ring, Nat.shiftRight_add]
    congr 2
    rw [Nat.shiftRight_eq_div_pow]
    have := code_lt g
    omega

theorem wordLetter_code (X Y Yi : ℕ) (g : Gen) : wordLetter X Y Yi (code g) = Gen.eval X Y g := by
  cases g <;> rfl

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

theorem pkMat_wordAB_range
    (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true) (X Y Yi W : ℕ) :
    ∀ n, pkMat (BigS.wordAB c rm ONE X Y Yi W n) =
      ((List.range n).map fun i => pkMat (wordLetter X Y Yi (BigS.bitsN W (2 * i) 2))).prod
  | 0 => by rw [pkMat_wordAB_zero hk, List.range_zero, List.map_nil, List.prod_nil]
  | n + 1 => by
    rw [pkMat_wordAB_succ hk, pkMat_wordAB_range hk X Y Yi W n, List.range_succ, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton]

end Consts

end CFSG.KC.Th.Max3S

end
