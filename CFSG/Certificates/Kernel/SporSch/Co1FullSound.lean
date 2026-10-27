module

public import Certificates.Data.Kernel.SporSch.Co1Full
public import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.KS.Raw CFSG.KS.SporSch.VOrb Matrix

@[expose] def qForm (a : Fin 24 → ZMod 2) (U : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (v : Fin 24 → ZMod 2) : ZMod 2 :=
  a ⬝ᵥ v + v ⬝ᵥ (U *ᵥ v)

theorem mulWM_eq (X Y : Nat) : rowsMatrix 24 (unpack 24 24 (CFSG.KC.Co1B.mulWK X Y)) =
    rowsMatrix 24 (unpack 24 24 X) * rowsMatrix 24 (unpack 24 24 Y) := by
  rw [← mul_unpackW]
  exact rowsMatrix_mulRows 24 _ _

theorem actK_sound (X v : Nat) :
    rowsMatrix 24 (unpack 24 24 X) *ᵥ toVecD 24 v = toVecD 24 (actK X v) := by
  rw [rowsMatrix_mulVec, ActL.vecMulN_unpack]

private theorem bits_testBit (g : Nat → Nat) (b : Nat) : ∀ l : List Nat,
    (l.foldr (fun j t => Nat.lor t (Nat.shiftLeft (Nat.land (g j) (nat_lit 1)) j)) 0).testBit b =
      (decide (b ∈ l) && (g b).testBit 0)
  | [] => by simp
  | x :: l => by
    rw [List.foldr_cons]
    change ((l.foldr (fun j t => Nat.lor t (Nat.shiftLeft (Nat.land (g j) (nat_lit 1)) j)) 0) |||
      ((g x &&& 2 ^ 0) <<< x)).testBit b = _
    rw [Nat.testBit_or, bits_testBit g b l, Nat.testBit_shiftLeft, Nat.testBit_and,
      Nat.testBit_two_pow]
    by_cases h : b = x
    · subst h
      simp
    · have h1 : decide (0 = b - x) = false ∨ decide (x ≤ b) = false := by
        by_cases hx : x ≤ b
        · left; simp only [decide_eq_false_iff_not]; omega
        · right; simp [hx]
      rcases h1 with h1 | h1 <;> simp [h1, h, List.mem_cons]

private noncomputable def trRow (X i : Nat) : Nat :=
  CFSG.KC.Enum.foldN 24 (fun j t => Nat.lor t
    (Nat.shiftLeft (Nat.land (Nat.shiftRight (rowK X j) i) (nat_lit 1)) j)) 0

private theorem trRow_testBit (X i b : Nat) :
    (trRow X i).testBit b = (decide (b < 24) && (rowK X b).testBit i) := by
  rw [trRow, MatL.foldN_eq, bits_testBit]
  simp only [List.mem_range]
  rw [show (rowK X b).shiftRight i = rowK X b >>> i from rfl, Nat.testBit_shiftRight, Nat.add_zero]

theorem trM_sound (X : Nat) :
    rowsMatrix 24 (unpack 24 24 (trK X)) = (rowsMatrix 24 (unpack 24 24 X))ᵀ := by
  have hf : ∀ i < 24, trRow X i < 2 ^ 24 := fun i _ =>
    Nat.lt_pow_two_of_testBit _ fun b hb => by
      rw [trRow_testBit]
      simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
      omega
  have e : trK X =
      CFSG.KC.Enum.foldN 24 (fun i s => Nat.lor s (Nat.shiftLeft (trRow X i) (Nat.mul 24 i))) 0 :=
    rfl
  rw [e, MatL.unpack_pack _ hf]
  ext i j
  rw [rowsMatrix_apply, Matrix.transpose_apply, rowsMatrix_apply, MatL.unpack_getD X j j.isLt,
    Array.getElem?_ofFn]
  simp only [i.isLt, ↓reduceDIte, Option.getD_some, toVecD_apply, trRow_testBit, j.isLt,
    decide_true, Bool.true_and, MatL.rowK_eq]

private theorem rowV_xor (X Y i : Nat) :
    MatL.rowV (X ^^^ Y) i = MatL.rowV X i ^^^ MatL.rowV Y i := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [MatL.rowV, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  cases decide (b < 24) <;> simp

theorem xorM_sound (X Y : Nat) : rowsMatrix 24 (unpack 24 24 (Nat.xor X Y)) =
    rowsMatrix 24 (unpack 24 24 X) + rowsMatrix 24 (unpack 24 24 Y) := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply,
    MatL.unpack_getD _ _ i.isLt, MatL.unpack_getD _ _ i.isLt, MatL.unpack_getD _ _ i.isLt]
  change toVecD 24 (MatL.rowV (X ^^^ Y) i) j = _
  rw [rowV_xor, toVecD_xor, Pi.add_apply]

private theorem castZ2 (n : Nat) : ((n : ℕ) : ZMod 2) = if n.testBit 0 then 1 else 0 := by
  rw [← ZMod.natCast_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

private theorem cast_xor (x y : Nat) : ((Nat.xor x y : ℕ) : ZMod 2) = (x : ZMod 2) + y := by
  change ((x ^^^ y : ℕ) : ZMod 2) = _
  rw [castZ2, castZ2 x, castZ2 y, Nat.testBit_xor]
  cases x.testBit 0 <;> cases y.testBit 0 <;> decide

private theorem xs_cast (f : Nat → Bool) (n : Nat) :
    (if ActL.xs f (List.range n) then (1 : ZMod 2) else 0) =
      ∑ j ∈ Finset.range n, if f j then 1 else 0 := by
  induction n with
  | zero => simp [ActL.xs_nil]
  | succ n ih =>
    rw [List.range_succ, ActL.xs_append, Finset.sum_range_succ, ← ih, ActL.xs_cons, ActL.xs_nil]
    cases ActL.xs f (List.range n) <;> cases f n <;> decide

private theorem dot_parK {r : Nat} (hr : r < 2 ^ 24) (s : Nat) :
    toVecD 24 r ⬝ᵥ toVecD 24 s = ((parK (Nat.land r s) : ℕ) : ZMod 2) := by
  have hp : (parK (Nat.land r s)).testBit 0 = Nat.beq (parK (Nat.land r s)) 1 := by
    rw [ActL.parK_eq, ActL.and_one_beq, Nat.testBit_and]
    simp
  rw [castZ2, hp, ActL.parK_and r s hr, xs_cast, dotProduct,
    ← Fin.sum_univ_eq_sum_range (fun j => if (r.testBit j && s.testBit j) then (1 : ZMod 2) else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [toVecD_apply]
  cases r.testBit j <;> cases s.testBit j <;> simp

private theorem toVecD_mask (x : Nat) : toVecD 24 (Nat.land x 16777215) = toVecD 24 x := by
  funext j
  have hm : (16777215 : Nat) = 2 ^ 24 - 1 := by norm_num
  change toVecD 24 (x &&& 16777215) j = _
  rw [toVecD_apply, toVecD_apply, Nat.testBit_and, hm, Nat.testBit_two_pow_sub_one]
  simp [j.isLt]

private theorem mask_lt (x : Nat) : Nat.land x 16777215 < 2 ^ 24 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem quadK_sound (a U v : Nat) :
    qForm (toVecD 24 a) (rowsMatrix 24 (unpack 24 24 U)) (toVecD 24 v) =
      ((quadK a U v : ℕ) : ZMod 2) := by
  unfold quadK qForm
  rw [MatL.strictN_eq, ← toVecD_mask v, ← toVecD_mask a, actK_sound, dot_parK (mask_lt a),
    dot_parK (mask_lt v), cast_xor]

private theorem cnt_fold (P : Nat → Bool) (n lo : Nat) : ∀ (L c : Nat),
    (List.range L).foldl (fun c d => if Nat.blt (lo + d) n = true then
      (if P (lo + d) = true then c + 1 else c) else c) c =
      c + ∑ d ∈ Finset.range L, if lo + d < n ∧ P (lo + d) = true then 1 else 0
  | 0, c => by simp
  | L + 1, c => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, cnt_fold P n lo L c,
      Finset.sum_range_succ]
    by_cases h1 : lo + L < n
    · have hb : Nat.blt (lo + L) n = true := Nat.blt_eq.mpr h1
      by_cases h2 : P (lo + L) = true <;> simp [hb, h1, h2, Nat.add_assoc]
    · have hb : Nat.blt (lo + L) n = false := by
        cases hq : Nat.blt (lo + L) n
        · rfl
        · exact absurd (Nat.blt_eq.mp hq) h1
      simp [hb, h1]

theorem cntSl_sound {T S C : Nat → Nat} {n w N NS L : Nat} (hL : n ≤ NS * L) (hc0 : C 0 = 0)
    (hcN : C NS = N) (h : ∀ s < NS, cntSl T S n w (s * L) L (C s) (C (s + 1)) = true) :
    ((Finset.range n).filter fun k => memK T S n (Nat.xor (ptK T k) w) = true).card = N := by
  have key : ∀ s ≤ NS, C s = ∑ k ∈ Finset.range (s * L),
      if k < n ∧ memK T S n (Nat.xor (ptK T k) w) = true then 1 else 0 := by
    intro s
    induction s with
    | zero => intro _; simp [hc0]
    | succ s ih =>
      intro hs
      have h1 := h s (by omega)
      unfold cntSl at h1
      have h2 := Nat.eq_of_beq_eq_true h1
      rw [Orb.foldUp_eq] at h2
      simp only [MatL.strictN_eq, MatL.nIf_eq, Nat.add_eq, Nat.succ_eq_add_one] at h2
      rw [cnt_fold (fun k => memK T S n (Nat.xor (ptK T k) w))] at h2
      rw [Nat.succ_mul, Finset.sum_range_add, ← ih (by omega), ← h2]
  rw [Finset.card_filter, ← hcN, key NS le_rfl, ← Finset.sum_range_add_sum_Ico _ hL]
  rw [Finset.sum_eq_zero (s := Finset.Ico n (NS * L)) fun k hk => by
    rw [Finset.mem_Ico] at hk
    simp [Nat.not_lt.mpr hk.1], Nat.add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  simp [hk]

end CFSG.KS.SporSch.M24

end
