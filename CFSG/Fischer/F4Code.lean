module

public import CFSG.Fischer.F4
public import Certificates.Data.CFSGNative.F4.Basic
public import Mathlib.Data.LawfulXor.Basic

public section

namespace CFSG.Fischer

open CFSG.F4.Native

theorem code_mul (x y : F4) : (x * y).code.val = f4mul x.code.val y.code.val := by
  revert x y; decide

theorem code_add (x y : F4) : (x + y).code.val = x.code.val ^^^ y.code.val := by
  revert x y; decide

theorem code_zero : (0 : F4).code.val = 0 := rfl

theorem code_lt (x : F4) : x.code.val < 4 := x.code.isLt

theorem code_inj {x y : F4} (h : x.code.val = y.code.val) : x = y := by
  cases x; cases y; simp only [F4.mk.injEq]; exact Fin.ext h

@[expose] def codeOf (v : Fin 6 → F4) : ℕ :=
  (v 0).code.val + 4 * (v 1).code.val + 16 * (v 2).code.val + 64 * (v 3).code.val +
    256 * (v 4).code.val + 1024 * (v 5).code.val

theorem codeOf_lt (v : Fin 6 → F4) : codeOf v < 4096 := by
  have := code_lt (v 0); have := code_lt (v 1); have := code_lt (v 2)
  have := code_lt (v 3); have := code_lt (v 4); have := code_lt (v 5)
  unfold codeOf; omega

theorem coord_codeOf (v : Fin 6 → F4) (i : Fin 6) : coord (codeOf v) i.val = (v i).code.val := by
  have := code_lt (v 0); have := code_lt (v 1); have := code_lt (v 2)
  have := code_lt (v 3); have := code_lt (v 4); have := code_lt (v 5)
  unfold coord codeOf
  fin_cases i <;> simp <;> omega

@[expose] def vecOfCode (c : ℕ) : Fin 6 → F4 := fun i => ⟨⟨coord c i.val, by unfold coord; omega⟩⟩

theorem vecOfCode_codeOf (v : Fin 6 → F4) : vecOfCode (codeOf v) = v := by
  funext i
  apply code_inj
  show coord (codeOf v) i.val = _
  exact coord_codeOf v i

theorem foldl_xor_six (f : ℕ → ℕ) :
    (List.range 6).foldl (fun acc i => acc ^^^ f i) 0 =
      f 0 ^^^ f 1 ^^^ f 2 ^^^ f 3 ^^^ f 4 ^^^ f 5 := by
  simp [List.range_succ]

@[expose] def hermStd (x y : Fin 6 → F4) : F4 := ∑ i, x i * (y i) ^ 2

theorem code_sum_six (f : Fin 6 → F4) :
    (∑ i, f i).code.val =
      (f 0).code.val ^^^ (f 1).code.val ^^^ (f 2).code.val ^^^ (f 3).code.val ^^^
        (f 4).code.val ^^^ (f 5).code.val := by
  rw [Fin.sum_univ_six, code_add, code_add, code_add, code_add, code_add]

theorem hermC_codeOf (x y : Fin 6 → F4) : hermC (codeOf x) (codeOf y) = (hermStd x y).code.val := by
  unfold hermC hermStd
  rw [foldl_xor_six, code_sum_six]
  simp only [pow_two, code_mul]
  have hx : ∀ k : Fin 6, coord (codeOf x) k.val = (x k).code.val := coord_codeOf x
  have hy : ∀ k : Fin 6, coord (codeOf y) k.val = (y k).code.val := coord_codeOf y
  have h0x : coord (codeOf x) 0 = (x 0).code.val := hx 0
  have h1x : coord (codeOf x) 1 = (x 1).code.val := hx 1
  have h2x : coord (codeOf x) 2 = (x 2).code.val := hx 2
  have h3x : coord (codeOf x) 3 = (x 3).code.val := hx 3
  have h4x : coord (codeOf x) 4 = (x 4).code.val := hx 4
  have h5x : coord (codeOf x) 5 = (x 5).code.val := hx 5
  have h0y : coord (codeOf y) 0 = (y 0).code.val := hy 0
  have h1y : coord (codeOf y) 1 = (y 1).code.val := hy 1
  have h2y : coord (codeOf y) 2 = (y 2).code.val := hy 2
  have h3y : coord (codeOf y) 3 = (y 3).code.val := hy 3
  have h4y : coord (codeOf y) 4 = (y 4).code.val := hy 4
  have h5y : coord (codeOf y) 5 = (y 5).code.val := hy 5
  rw [h0x, h1x, h2x, h3x, h4x, h5x, h0y, h1y, h2y, h3y, h4y, h5y]

end CFSG.Fischer
