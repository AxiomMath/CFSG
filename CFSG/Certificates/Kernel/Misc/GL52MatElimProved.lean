module

public import CFSG.Certificates.Kernel.Misc.GL52MatCode
import CFSG.Certificates.Kernel.Misc.GL52MatProved
import CFSG.Certificates.Kernel.Misc.GL52Sol
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.Rank

namespace CFSG.KC.Misc.GLM

open CFSG.KC.Misc.GLM.Pf CFSG.KC.Misc.GLM.Ech

theorem zb_val : ∀ x : ZMod 2, (if zb x = true then (1 : ZMod 2) else 0) = x := by decide

theorem bvo_row (A : Mat) (i : Fin 5) : bvo 5 0 (rowK (mcode A) i) = A i := by
  funext j
  change (if (rowK (mcode A) i).testBit (j + 0) then (1 : ZMod 2) else 0) = A i j
  rw [Nat.add_zero, rowK_bit, decide_eq_true j.isLt, Bool.true_and, mcode_bit]
  exact zb_val _

theorem bvo_mcode (A : Mat) : bvo 25 0 (mcode A) = vec A := by
  funext q
  change (if (mcode A).testBit (q + 0) then (1 : ZMod 2) else 0) = A ⟨q / 5, _⟩ ⟨q % 5, _⟩
  have e : (q : ℕ) + 0 = 5 * ((⟨q / 5, by omega⟩ : Fin 5) : ℕ) + ((⟨q % 5, by omega⟩ : Fin 5) : ℕ) := by
    simp only
    omega
  rw [e, mcode_bit]
  exact zb_val _

theorem unit_mcode (idx : ℕ) (hidx : idx < 25) :
    Nat.shiftLeft 1 idx = mcode (mat (bvo 25 0 (2 ^ idx))) := by
  have h1 : Nat.shiftLeft 1 idx = 2 ^ idx := Nat.one_shiftLeft idx
  rw [h1]
  exact bvo25_inj (Nat.pow_lt_pow_right (by norm_num) hidx) (mcode_lt _)
    (by rw [bvo_mcode, vec_mat])

end CFSG.KC.Misc.GLM

public section

namespace CFSG.KC.Misc.GLM

open CFSG.KC.Misc.GLM.Ech

theorem rankK_mcode_proved (A : Mat) : rankK (mcode A) = A.rank :=
  rankK_rows (mcode A) A (bvo_row A)

theorem solCnt_sound_proved (ps : List (Mat × Mat)) :
    Nat.card {g : GL (Fin 5) (ZMod 2) // ∀ p ∈ ps, (g : Mat) * p.1 = p.2 * (g : Mat)} =
      unitCntK (elimK (ps.map fun p => (mcode p.1, mcode p.2)) (25 * ps.length) 25).2 :=
  sol_count mcode Pf.mcode_lt bvo_mcode rankK_mcode_proved mmulK_mcode_proved mcode_add_proved
    unit_mcode ps

end CFSG.KC.Misc.GLM

end
