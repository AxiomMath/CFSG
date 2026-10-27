module

public import Certificates.Data.Kernel.M24R.N8K
public import CFSG.Certificates.Kernel.F4M3BSound

public section

namespace CFSG.KC.N8K

open CFSG.CosetTable CFSG.CGT.T75JM CFSG.CGT.M24R CFSG.KC.F4M3B

theorem carm_card_le (h6 : subsetCheck carmR6 [0, 1, 2, 3, 4] 200 8 = true)
    (h5 : subsetCheck carmR5 [0, 1, 2, 3] 200 7 = true)
    (h4 : subsetCheck carmR4 [0, 1, 2] 200 6 = true)
    (h3 : subsetCheck carmR3 [0, 1] 200 5 = true)
    (h2 : subsetCheck carmR2 [0] 200 4 = true)
    (h1 : subsetCheck carmR1 [] 200 3 = true) :
    Finite (PG (subsetOf 10 [0, 1, 2, 3, 4, 5]).length carmRels8) ∧
      Nat.card (PG (subsetOf 10 [0, 1, 2, 3, 4, 5]).length carmRels8) ≤ 20160 := by
  obtain ⟨f1, c1⟩ := card_le_of_subsetCheck_nil carmR1 h1
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheck carmR2 [0] h2
  obtain ⟨f3, c3⟩ := card_le_of_subsetCheck carmR3 [0, 1] h3
  obtain ⟨f4, c4⟩ := card_le_of_subsetCheck carmR4 [0, 1, 2] h4
  obtain ⟨f5, c5⟩ := card_le_of_subsetCheck carmR5 [0, 1, 2, 3] h5
  obtain ⟨f6, c6⟩ := card_le_of_subsetCheck carmR6 [0, 1, 2, 3, 4] h6
  have b2 := c2.trans (Nat.mul_le_mul_left 4 c1)
  have b3 := c3.trans (Nat.mul_le_mul_left 5 b2)
  have b4 := c4.trans (Nat.mul_le_mul_left 6 b3)
  have b5 := c5.trans (Nat.mul_le_mul_left 7 b4)
  have b6 := c6.trans (Nat.mul_le_mul_left 8 b5)
  exact ⟨f6, b6.trans (by norm_num)⟩

theorem popc_eq : ∀ k x, popc k x = (List.range (2 ^ k)).countP fun i => x.testBit i
  | 0, x => by
    change x &&& 1 = _
    rw [Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, Nat.testBit_zero]
  | k + 1, x => by
    have e : popc (k + 1) x = popc k (x &&& (2 ^ 2 ^ k - 1)) + popc k (x >>> 2 ^ k) := rfl
    rw [e, popc_eq k, popc_eq k, pow_succ, mul_two, List.range_add, List.countP_append,
      List.countP_map]
    congr 1
    · apply List.countP_congr
      intro i hi
      rw [List.mem_range] at hi
      simp [Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, hi]
    · apply List.countP_congr
      intro i _
      simp [Nat.testBit_shiftRight]

theorem testBit_applyC (X : Cols) (v n : Nat) : (applyC X v).testBit n =
    ((v.testBit 0 && X.c0.testBit n) ^^ (v.testBit 1 && X.c1.testBit n) ^^
      (v.testBit 2 && X.c2.testBit n) ^^ (v.testBit 3 && X.c3.testBit n)) := by
  unfold applyC
  cases v.testBit 0 <;> cases v.testBit 1 <;> cases v.testBit 2 <;> cases v.testBit 3 <;>
    simp [Nat.testBit_xor]

theorem ne_zero_bits : ∀ n < 16, (n != 0) =
    (n.testBit 0 || n.testBit 1 || n.testBit 2 || n.testBit 3) := by decide

theorem colsOfCode8_lt (c : Nat) : ∀ j, (colsOfCode8 c).col j < 16 := by
  intro j
  fin_cases j <;> simp [colsOfCode8, Cols.col] <;> omega

theorem bit_mod16 (c b : Nat) (hb : b < 4) : (c % 16).testBit b = c.testBit b := by
  rw [show (16 : Nat) = 2 ^ 4 from rfl, Nat.testBit_mod_two_pow]
  simp [hb]

theorem bit_div16 (c k b : Nat) (hb : b < 4) : (c / 2 ^ k % 16).testBit b = c.testBit (b + k) := by
  rw [bit_mod16 _ _ hb, Nat.testBit_div_two_pow]

theorem glV_bit (A B C D : Cols) (v c : Nat) : (glV A B C D v).testBit c =
    (((applyC A v).testBit c || (applyC B v).testBit c) ||
      ((applyC C v).testBit c || (applyC D v).testBit c)) := by
  change ((applyC A v ||| applyC B v) ||| (applyC C v ||| applyC D v)).testBit c = _
  simp only [Nat.testBit_or]

theorem glAnd_bit (A B C D : Cols) (t c : Nat) : ∀ n, (glAnd A B C D t n).testBit c =
    (t.testBit c && (List.range n).all fun v => (glV A B C D (v + 1)).testBit c)
  | 0 => by
    change t.testBit c = _
    simp
  | n + 1 => by
    have e : glAnd A B C D t (n + 1) = glAnd A B C D t n &&& glV A B C D (n + 1) := by
      change frcN (glAnd A B C D t n) (fun a => Nat.land a (glV A B C D (n + 1))) = _
      rw [frcN_eq]
      rfl
    rw [e, Nat.testBit_and, glAnd_bit A B C D t c n, List.range_succ, List.all_append]
    simp [Bool.and_assoc]

theorem glPlane_eq : glPlane = glAnd ⟨pln 0 16, pln 4 16, pln 8 16, pln 12 16⟩
    ⟨pln 1 16, pln 5 16, pln 9 16, pln 13 16⟩ ⟨pln 2 16, pln 6 16, pln 10 16, pln 14 16⟩
    ⟨pln 3 16, pln 7 16, pln 11 16, pln 15 16⟩ (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1) 15 := by
  unfold glPlane glPlaneN
  repeat rw [frcN_eq]

set_option exponentiation.threshold 65536 in
theorem glPlane_bit (c : Nat) (hc : c < 65536) : glPlane.testBit c = isGL8 (colsOfCode8 c) := by
  have hc' : c < 2 ^ 16 := hc
  have ht : (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1).testBit c = true := by
    rw [Nat.sub_eq, Nat.pow_eq, Nat.pow_eq, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hc'
  rw [glPlane_eq, glAnd_bit, ht, Bool.true_and]
  unfold isGL8
  congr 1
  funext v
  rw [glV_bit, ne_zero_bits _ (applyC_lt (colsOfCode8_lt c) _)]
  have h0 : (colsOfCode8 c).c0 = c / 2 ^ 0 % 16 := by simp [colsOfCode8]
  have h1 : (colsOfCode8 c).c1 = c / 2 ^ 4 % 16 := rfl
  have h2 : (colsOfCode8 c).c2 = c / 2 ^ 8 % 16 := rfl
  have h3 : (colsOfCode8 c).c3 = c / 2 ^ 12 % 16 := rfl
  simp only [testBit_applyC, pln_bit, hc', decide_true, Bool.true_and, h0, h1, h2, h3,
    bit_div16 c _ 0 (by decide), bit_div16 c _ 1 (by decide), bit_div16 c _ 2 (by decide),
    bit_div16 c _ 3 (by decide), Nat.reduceAdd, Bool.or_assoc]

theorem glCount_of (h : glCountK = true) : glCountCheck = true := by
  unfold glCountK at h
  have h1 := Nat.eq_of_beq_eq_true h
  have e16 : (2 : Nat) ^ 16 = 65536 := by norm_num
  rw [popc_eq, e16] at h1
  have h2 : (allCols8.filter isGL8).length = 20160 := by
    rw [← h1, ← List.countP_eq_length_filter, allCols8, List.countP_map]
    apply List.countP_congr
    intro c hc
    rw [List.mem_range] at hc
    simp [glPlane_bit c hc]
  unfold glCountCheck natEqB8
  rw [h2]
  rfl

theorem modelCols8_lt' : ∀ i : Fin 6, ∀ j : Fin 4, (modelCols8 i).col j < 16 := by decide

theorem evalM8_lt : ∀ (w : List (Fin 6)) (j : Fin 4), (evalM8 w).col j < 16
  | [], j => by fin_cases j <;> decide
  | i :: w, j => by
    change (compC (modelCols8 i) (evalM8 w)).col j < 16
    fin_cases j <;> exact applyC_lt (modelCols8_lt' i) _

theorem colsOfCode8_colsCode8 (C : Cols) (h : ∀ j, C.col j < 16) :
    colsOfCode8 (colsCode8 C) = C := by
  obtain ⟨a, b, c, d⟩ := C
  have h0 : a < 16 := h 0
  have h1 : b < 16 := h 1
  have h2 : c < 16 := h 2
  have h3 : d < 16 := h 3
  simp only [colsOfCode8, colsCode8, Cols.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem lk_eq : ∀ i : Fin 6, ∀ v < 16, lk i.val v = applyC (modelCols8 i) v := by decide

theorem lk_eq' (i : Fin 6) (v : Nat) :
    lk i.val (Nat.mod v 16) = applyC (modelCols8 i) (v % 16) :=
  lk_eq i _ (Nat.mod_lt _ (by decide))

theorem stepT_eq (i : Fin 6) (x : Nat) : stepT i.val x = stepC i x := by
  unfold stepT stepC
  simp only [lk_eq']
  rfl

theorem evalC_eq : ∀ f n, evalC f n = colsCode8 (evalM8 (decW f n))
  | 0, _ => rfl
  | f + 1, n => by
    have e1 : decW (f + 1) n = @Bool.rec (fun _ => List (Fin 6))
        (letter8 n :: decW f (Nat.shiftRight n 3)) [] (Nat.beq n 0) := rfl
    have e2 : evalC (f + 1) n = @Bool.rec (fun _ => Nat)
        (frcN (evalC f (Nat.shiftRight n 3)) (stepT (letter8 n).val)) (colsCode8 idC)
        (Nat.beq n 0) := rfl
    rw [e1, e2]
    cases Nat.beq n 0
    · change frcN (evalC f (Nat.shiftRight n 3)) (stepT (letter8 n).val) =
        colsCode8 (compC (modelCols8 (letter8 n)) (evalM8 (decW f (Nat.shiftRight n 3))))
      rw [frcN_eq, evalC_eq f, stepT_eq, stepC, colsOfCode8_colsCode8 _ (evalM8_lt _)]
    · rfl

theorem glFreshK_cons (k : Nat → Nat → Bool) (n : Nat) (L : List Nat) (S cnt : Nat) :
    glFreshK k (n :: L) S cnt = (Nat.ble S (evalC 12 n) &&
      glFreshK k L (evalC 12 n + 1) (cnt + 1)) := by
  have e : glFreshK k (n :: L) S cnt = frc (evalC 12 n) (fun c =>
      Bool.and (Nat.ble S c) (frc (Nat.succ c) fun lo' =>
        frc (Nat.succ cnt) fun cnt' => glFreshK k L lo' cnt')) := rfl
  rw [e]
  simp only [frc_eq]

theorem glFreshK_append (k : Nat → Nat → Bool) (L₂ : List Nat) : ∀ (L₁ : List Nat) (S cnt : Nat),
    glFreshK k (L₁ ++ L₂) S cnt = glFreshK (glFreshK k L₂) L₁ S cnt
  | [], _, _ => rfl
  | n :: L₁, S, cnt => by
    rw [List.cons_append, glFreshK_cons, glFreshK_cons, glFreshK_append k L₂ L₁]

theorem glFresh_eq : ∀ (Ls : List (List Nat)) (S cnt : Nat),
    glFresh Ls S cnt = glFreshK glEnd Ls.flatten S cnt
  | [], _, _ => rfl
  | L :: Ls, S, cnt => by
    rw [List.flatten_cons, glFreshK_append]
    change glFreshK (glFresh Ls) L S cnt = _
    rw [show glFresh Ls = glFreshK glEnd Ls.flatten from
      funext fun S => funext fun c => glFresh_eq Ls S c]

theorem glFresh_sound : ∀ (L : List Nat) (S cnt : Nat), glFreshK glEnd L S cnt = true →
    cnt + L.length = 20160 ∧ (L.map fun n => evalC 12 n).Nodup ∧
      ∀ n ∈ L, S ≤ evalC 12 n
  | [], S, cnt, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, List.nodup_nil, by simp⟩
  | n :: L, S, cnt, h => by
    rw [glFreshK_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : S ≤ evalC 12 n := Nat.le_of_ble_eq_true h1
    obtain ⟨hl, hnd, hS⟩ := glFresh_sound L _ _ h2
    refine ⟨by simp only [List.length_cons] at hl ⊢; omega, ?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hnd⟩
      obtain ⟨m, hm, hmc⟩ := List.mem_map.1 hm
      beta_reduce at hmc
      have := hS m hm
      omega
    · intro m hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact h1'
      · have := hS m hm
        omega

theorem glWords_of {Ls : List (List Nat)} (h : glFresh Ls 0 0 = true) :
    ∃ W : List (List (Fin 6)), W.length = 20160 ∧ (W.map evalM8).Nodup := by
  rw [glFresh_eq] at h
  obtain ⟨hl, hnd, -⟩ := glFresh_sound Ls.flatten 0 0 h
  refine ⟨Ls.flatten.map (decW 12), by rw [List.length_map]; omega, ?_⟩
  rw [List.map_map]
  refine List.Nodup.of_map colsCode8 ?_
  rw [List.map_map]
  have e : (colsCode8 ∘ evalM8 ∘ decW 12) = fun n => evalC 12 n :=
    funext fun n => (evalC_eq 12 n).symm
  rw [e]
  exact hnd

end CFSG.KC.N8K

end
