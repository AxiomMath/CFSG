module

public import CFSG.LargeExtraspecial.Asc611IFrame
import all CFSG.Fischer.F4

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Matrix CFSG.Fischer CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

variable {r : ℕ}

@[expose] def tmatF (c : Fin r → F4) : Matrix (Fin r) (Fin r) F4 :=
  fun l b => (if l = b then 1 else 0) + c l ^ 2 * c b

@[expose] def stepF (M : Matrix (Fin r) (Fin r) F4) (c : Fin r → F4) :
    Matrix (Fin r) (Fin r) F4 :=
  M + ((tmatF c).map (· ^ 2))ᵀ * M * tmatF c

@[expose] def rk1F (d : Fin r → F4) : Matrix (Fin r) (Fin r) F4 := fun l l' => d l ^ 2 * d l'

theorem map_tmatF (c : Fin r → F4) : (tmatF c).map eF4 = tmat (fun i => eF4 (c i)) := by
  ext l b
  simp only [Matrix.map_apply, tmatF, tmat, map_add, map_mul, frob_eF4, apply_ite eF4,
    map_one, map_zero]

theorem map_sq_map (A : Matrix (Fin r) (Fin r) F4) :
    (A.map (· ^ 2)).map eF4 = (A.map eF4).map frob := by
  ext l b
  simp only [Matrix.map_apply, frob_eF4]

theorem map_stepF (M : Matrix (Fin r) (Fin r) F4) (c : Fin r → F4) :
    (stepF M c).map eF4 = M.map eF4 + ((tmat (fun i => eF4 (c i))).map frob)ᵀ * M.map eF4 *
      tmat (fun i => eF4 (c i)) := by
  rw [stepF, Matrix.map_add, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    map_sq_map, map_tmatF]
  exact fun a b => map_add eF4 a b

theorem map_rk1F (d : Fin r → F4) :
    (rk1F d).map eF4 = fun l l' => frob (eF4 (d l)) * eF4 (d l') := by
  ext l l'
  simp only [Matrix.map_apply, rk1F, map_mul, frob_eF4, map_pow]

theorem norm_eF4 {c : Fin r → F4} (h : ∑ i, c i ^ 2 * c i = 0) :
    ∑ i, frob (eF4 (c i)) * eF4 (c i) = 0 := by
  simp only [frob_eF4, ← map_mul, ← map_sum, h, map_zero]

abbrev wF : F4 := ⟨2⟩

abbrev w2F : F4 := ⟨3⟩

@[expose] def hpF (r : ℕ) : Matrix (Fin r) (Fin r) F4 :=
  fun l l' => if l = l' ∧ l.val < 2 then 1 else 0

@[expose] def m0F (r : ℕ) : Matrix (Fin r) (Fin r) F4 :=
  fun l l' => if l.val = 0 ∧ l'.val = 1 then w2F else if l.val = 1 ∧ l'.val = 0 then wF else 0

theorem chainF_r2_M0 : m0F 2 + 1 = rk1F ![1, w2F] := by decide

theorem chainF_r3_HP : hpF 3 + 1 = rk1F ![0, 0, 1] := by decide

theorem chainF_r3_M0 : stepF (stepF (m0F 3) ![0, 1, 1]) ![1, 0, 1] + 1 = rk1F ![1, w2F, 1] := by
  decide

theorem chainF_r4_HP : stepF (stepF (hpF 4) ![0, 1, 0, 1] + stepF (hpF 4) ![1, 1, 1, 1])
    ![1, wF, 1, wF] = rk1F ![1, wF, 1, wF] := by decide

theorem chainF_r4_M0 : stepF (stepF (m0F 4) ![0, 1, 0, 1] + stepF (m0F 4) ![1, 1, 1, 1])
    ![1, 0, 1, 0] = rk1F ![1, 0, 1, 0] := by decide

end CFSG.LargeExtraspecial.Asc611I
