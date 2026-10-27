module

public import CFSG.Certificates.Kernel.O8OrthMatProved

public section

namespace CFSG.KC.O8.WordPf

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.O8 CFSG.KC.O8.OrthPf
  CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1

theorem frow_lt (M i : ℕ) : frow M i < 64 := fget_lt M i 6

theorem xf_false (k : ℕ) : xorFold k (fun _ => false) = false := by
  induction k with
  | zero => rfl
  | succ k ih => rw [xorFold_succ, ih]; rfl

theorem testBit_frow (M i j : ℕ) : (frow M i).testBit j = (decide (j < 6) && M.testBit (6 * i + j)) := by
  rw [frow, testBit_fget, Nat.mul_comm i 6]

theorem decR_size (P : ℕ) : (decR P).size = 6 := rfl

theorem arr6_ext {A B : Array ℕ} (hA : A.size = 6) (hB : B.size = 6)
    (h : ∀ i < 6, A.getD i 0 = B.getD i 0) : A = B := by
  apply Array.ext (by rw [hA, hB])
  intro i h1 h2
  have e := h i (by omega)
  simpa [Array.getD_eq_getD_getElem?, h1, h2] using e

theorem bmul_size (A B : Array ℕ) : (bmul 6 6 A B).size = 6 := by
  rw [bmul, Array.size_ofFn]

theorem bmulK_testBit (A B : ℕ) {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    (bmulK A B).testBit (6 * i + j) =
      xorFold 6 fun l => (frow A i).testBit l && (frow B l).testBit j := by
  by_cases hA : A = 0
  · subst hA
    have e : bmulK 0 B = 0 := rfl
    rw [e, Nat.zero_testBit, ← xf_false 6]
    apply xorFold_congr
    intro l _
    rw [show frow 0 i = 0 from by rw [frow, fget_eq]; simp, Nat.zero_testBit, Bool.false_and]
  by_cases hB : B = 0
  · subst hB
    have e : bmulK A 0 = 0 := by
      change strictN A (fun A => nIf(Nat.beq A (nat_lit 0), nat_lit 0, nat_lit 0)) = 0
      rw [strictN_eq, nIf_eq]
      split <;> rfl
    rw [e, Nat.zero_testBit, ← xf_false 6]
    apply xorFold_congr
    intro l _
    rw [show frow 0 l = 0 from by rw [frow, fget_eq]; simp, Nat.zero_testBit, Bool.and_false]
  have hb : bmulK A B = orN 6 fun i => (xorN 6 fun l =>
      nIf(Nat.beq (bitN (frow A i) l) (nat_lit 1), frow B l, nat_lit 0)) <<< (6 * i) := by
    change strictN A (fun A => nIf(Nat.beq A (nat_lit 0), nat_lit 0, strictN B fun B =>
      nIf(Nat.beq B (nat_lit 0), nat_lit 0, orN (nat_lit 6) fun i => Nat.shiftLeft
        (xorN (nat_lit 6) fun l => nIf(Nat.beq (bitN (frow A i) l) (nat_lit 1), frow B l, nat_lit 0))
        (Nat.mul (nat_lit 6) i)))) = _
    rw [strictN_eq]
    beta_reduce
    rw [nIf_eq, if_neg (fun h' => hA (Nat.eq_of_beq_eq_true h')), strictN_eq]
    beta_reduce
    rw [nIf_eq, if_neg (fun h' => hB (Nat.eq_of_beq_eq_true h'))]
    rfl
  rw [hb, testBit_orN_rows (fun i _ => xorN_lt 6 _ (fun l _ => by
      rw [nIf_eq]
      split
      · exact fget_lt _ _ _
      · omega)) hi hj, testBit_xorN]
  apply xorFold_congr
  intro l _
  rw [nIf_eq, beq_bitN]
  cases (frow A i).testBit l <;> simp

theorem frow_bmulK (A B : ℕ) {i : ℕ} (hi : i < 6) :
    frow (bmulK A B) i = rowMul 6 (frow A i) (decR B) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_frow, testBit_rowMul]
  by_cases hj : j < 6
  · rw [decide_eq_true hj, Bool.true_and, bmulK_testBit A B hi hj]
    apply xorFold_congr
    intro l hl
    rw [decR_getD B hl]
  · rw [decide_eq_false hj, Bool.false_and, ← xf_false 6]
    apply xorFold_congr
    intro l hl
    rw [decR_getD B hl, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (frow_lt B l)
      (by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 6 ≤ j))), Bool.and_false]

theorem decR_bmulK (A B : ℕ) : decR (bmulK A B) = bmul 6 6 (decR A) (decR B) := by
  apply arr6_ext (decR_size _) (bmul_size _ _)
  intro i hi
  rw [decR_getD _ hi, bmul_getD hi, decR_getD _ hi, frow_bmulK A B hi]

theorem decR_ID6 : decR ID6 = id6 := by decide +kernel

theorem wordRowsK_eq {GP : ℕ} {G : ℕ → Array ℕ} (hG : ∀ s < 6, G s = decR (mat GP s)) :
    ∀ (w : List ℕ), (∀ s ∈ w, s < 6) → decR (wordRowsK GP w) = wordRowsG G w
  | [], _ => decR_ID6
  | s :: w, hw => by
    change decR (bmulK (mat GP s) (wordRowsK GP w)) = bmul 6 6 (G s) (wordRowsG G w)
    rw [decR_bmulK, wordRowsK_eq hG w (fun t ht => hw t (by simp [ht])), hG s (hw s (by simp))]

theorem decR_inj {A B : ℕ} (hA : A < 2 ^ 36) (hB : B < 2 ^ 36) (h : decR A = decR B) : A = B := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 36
  · have h1 : (decR A).getD (p / 6) 0 = (decR B).getD (p / 6) 0 := by rw [h]
    rw [decR_getD _ (by omega), decR_getD _ (by omega)] at h1
    have h2 := congrArg (fun x => Nat.testBit x (p % 6)) h1
    simp only [testBit_frow, decide_eq_true (Nat.mod_lt p (by omega : 6 > 0)), Bool.true_and] at h2
    rwa [Nat.div_add_mod] at h2
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hB (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem decR_beq {A B : ℕ} (hA : A < 2 ^ 36) (hB : B < 2 ^ 36) :
    (decR A == decR B) = Nat.beq A B := by
  by_cases h : A = B
  · subst h
    rw [beq_self_eq_true, Nat.beq_refl]
  · rw [Bool.eq_false_iff.2 (fun h' => h (Nat.eq_of_beq_eq_true h')), beq_eq_false_iff_ne]
    exact fun h' => h (decR_inj hA hB h')

theorem mat_lt (L k : ℕ) : mat L k < 2 ^ 36 := fget_lt L k 36

end CFSG.KC.O8.WordPf

end
