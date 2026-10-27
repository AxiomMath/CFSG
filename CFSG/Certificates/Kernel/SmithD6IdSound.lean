module

public import Certificates.Data.Kernel.SmithD6.IdCheck
public import CFSG.GF2Type.SmithTypeE.DMod.CliffordEx
import CFSG.Certificates.Kernel.SmithD6WtSound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.GF2Type.SmithTypeE.DMod

theorem testBit_xorFold_sel (p : ℕ → Bool) (n j : ℕ) :
    (xorFold n fun k => bif p k then 2 ^ k else 0).testBit j = (decide (j < n) && p j) := by
  induction n with
  | zero => simp [xorFold_zero]
  | succ n ih =>
    rw [xorFold_succ, Nat.testBit_xor, ih]
    by_cases hj : j < n
    · have h1 : j < n + 1 := by omega
      have h2 : n ≠ j := by omega
      cases hs : p n <;> simp [hj, h1, h2, Nat.testBit_two_pow]
    · by_cases hjn : j = n
      · subst hjn
        cases hs : p j <;> simp [hj, hs, Nat.testBit_two_pow]
      · have h1 : ¬ j < n + 1 := by omega
        have h2 : n ≠ j := by omega
        cases hs : p n <;> simp [hj, h1, h2, Nat.testBit_two_pow]

theorem testBit_rev32 (d t : ℕ) : (rev32 d).testBit t = (decide (t < 32) && d.testBit (31 - t)) :=
  testBit_xorFold_sel (fun t => d.testBit (31 - t)) 32 t

theorem testBit_pfold (k x j : ℕ) : (pfold k x).testBit j = (x.testBit j ^^ x.testBit (k + j)) := by
  unfold pfold
  change (x ^^^ (x >>> k)).testBit j = _
  rw [Nat.testBit_xor, Nat.testBit_shiftRight]

theorem range_32 : List.range 32 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
    18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := rfl

theorem bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem fB_eq_fBK (s d : ℕ) : fB s d = fBK s (rev32 d) := by
  have hb : ∀ i, i < 32 → (Nat.land s (rev32 d)).testBit i = (s.testBit i && d.testBit (31 - i)) := by
    intro i hi
    change (s &&& rev32 d).testBit i = _
    rw [Nat.testBit_and, testBit_rev32, decide_eq_true hi, Bool.true_and]
  apply bit_injective
  unfold fBK fB
  simp only [testBit_pfold, range_32, List.foldl_cons, List.foldl_nil, Nat.reduceAdd,
    Bool.false_xor, bit_xor]
  rw [hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num),
    hb 4 (by norm_num), hb 5 (by norm_num), hb 6 (by norm_num), hb 7 (by norm_num),
    hb 8 (by norm_num), hb 9 (by norm_num), hb 10 (by norm_num), hb 11 (by norm_num),
    hb 12 (by norm_num), hb 13 (by norm_num), hb 14 (by norm_num), hb 15 (by norm_num),
    hb 16 (by norm_num), hb 17 (by norm_num), hb 18 (by norm_num), hb 19 (by norm_num),
    hb 20 (by norm_num), hb 21 (by norm_num), hb 22 (by norm_num), hb 23 (by norm_num),
    hb 24 (by norm_num), hb 25 (by norm_num), hb 26 (by norm_num), hb 27 (by norm_num),
    hb 28 (by norm_num), hb 29 (by norm_num), hb 30 (by norm_num), hb 31 (by norm_num)]
  try simp only [Nat.reduceSub]
  ring

theorem fB_congr {a b : ℕ} (h : decode32 a = decode32 b) (w : ℕ) : fB w a = fB w b := by
  have hbit : ∀ t, a.testBit (31 - t) = b.testBit (31 - t) := by
    intro t
    have := congrFun h ⟨31 - t, by omega⟩
    simp only [decode32_apply] at this
    cases ha : a.testBit (31 - t) <;> cases hb : b.testBit (31 - t) <;> simp_all
  unfold fB
  simp only [hbit]

theorem tvCols_size (k : ℕ) : (tvCols k).size = 32 := by
  unfold tvCols
  simp

theorem tvCols_lt (k : ℕ) {c : ℕ} (hc : c < 32) : (tvCols k)[c]! < 2 ^ 32 := by
  rw [tvCols_getElem k hc]
  refine Nat.xor_lt_two_pow ?_ (Nat.pow_lt_pow_right (by norm_num) hc)
  exact Nat.and_lt_two_pow _ (by norm_num)

theorem foldl_applyCols_lt (cols : Array ℕ) (c : ℕ) (h : ∀ m < cols.size, cols[m]! < 2 ^ 32) :
    ∀ n, n ≤ cols.size → ∀ a < 2 ^ 32,
      (List.range n).foldl (fun acc m => if c.testBit m then acc ^^^ cols[m]! else acc) a < 2 ^ 32 := by
  intro n
  induction n with
  | zero => intro _ a ha; exact ha
  | succ n ih =>
    intro hn a ha
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have := ih (by omega) a ha
    split_ifs
    · exact Nat.xor_lt_two_pow this (h n (by omega))
    · exact this

theorem applyCols_tvCols_lt (k x : ℕ) : applyCols (tvCols k) x < 2 ^ 32 := by
  unfold applyCols
  exact foldl_applyCols_lt _ _ (fun m hm => tvCols_lt k (by rw [tvCols_size] at hm; exact hm)) _
    le_rfl 0 (by norm_num)

theorem w64_add_self (y : W64) : y + y = 0 := by
  funext T
  exact zmod2_add_self _

theorem id7Vec_decode {k u w x v : ℕ} (hl : linePair k = (u, w))
    (hv : exC v = rhoK u (rhoK w (exC x))) :
    decode32 v = decode32 (applyCols (tvCols k) x ^^^ x) := by
  apply exL_injective
  rw [← decode64_exC, hv, rhoK_eq, rhoK_eq, decode64_rhoC, decode64_rhoC, decode64_exC,
    decode32_xor, decode32_applyCols (tvCols_size k), map_add, exL_colsLin_tvCols, hl]
  simp only [tlift, LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply]
  rw [add_right_comm, w64_add_self, zero_add]

theorem id7VecOK_sound {u w x : ℕ} (h : id7VecOK u w x = true) :
    id7VecK u w x < 2 ^ 32 ∧ exC (id7VecK u w x) = rhoK u (rhoK w (exC x)) := by
  unfold id7VecOK at h
  obtain ⟨h1, h2⟩ := band_true h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem id7Vec_eq {k u w x : ℕ} (hl : linePair k = (u, w)) (h : id7VecOK u w x = true)
    (hx : x < 2 ^ 32) : id7VecK u w x = applyCols (tvCols k) x ^^^ x := by
  obtain ⟨h1, h2⟩ := id7VecOK_sound h
  exact eq_of_decode32_eq h1 (Nat.xor_lt_two_pow (applyCols_tvCols_lt k x) hx)
    (id7Vec_decode hl h2)

theorem id7ProjP_cons (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) (s : ℕ) :
    id7ProjP (p :: ps) s = (if fBK s p.1 then p.2 else 0) ^^^ id7ProjP ps s := by
  change Nat.xor (nIf(fBK s p.1, p.2, 0)) (id7ProjP ps s) = _
  cases fBK s p.1 <;> rfl

theorem foldl_id7ProjP (s : ℕ) : ∀ (ps : List (ℕ × ℕ)) (a : ℕ),
    ps.foldl (fun acc p => if fBK s p.1 then acc ^^^ p.2 else acc) a = a ^^^ id7ProjP ps s
  | [], a => by
    change a = a ^^^ 0
    rw [Nat.xor_zero]
  | p :: ps, a => by
    rw [List.foldl_cons, foldl_id7ProjP s ps, id7ProjP_cons]
    split_ifs
    · rw [Nat.xor_assoc]
    · rw [Nat.zero_xor]

theorem id7QaGo_sound {ps : List (ℕ × ℕ)} :
    ∀ l : List ℕ, id7QaGo ps l = true → ∀ s ∈ l, id7QaWtOK ps s = true
  | [], _, s, hs => absurd hs List.not_mem_nil
  | x :: l, h, s, hs => by
    have e : id7QaGo ps (x :: l) = bAnd(id7QaWtOK ps x, id7QaGo ps l) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h1
    · exact id7QaGo_sound l h2 s hs

theorem id7QaWtOK_sound {ps : List (ℕ × ℕ)} {s : ℕ} (h : id7QaWtOK ps s = true) :
    (s = 1 ∨ wtTree.memB (1 ^^^ s) = true) ↔ id7ProjP ps s = s := by
  revert h
  unfold id7QaWtOK
  change Bool.rec _ _ (Bool.rec (KT.memB (1 ^^^ s) wtTree) true (Nat.beq s 1)) = true → _
  cases h1 : Nat.beq s 1 <;> cases h2 : KT.memB (1 ^^^ s) wtTree <;>
    cases h3 : Nat.beq (id7ProjP ps s) s <;> intro h <;>
    simp_all [Nat.eq_of_beq_eq_true, Nat.ne_of_beq_eq_false]

end CFSG.KD.SmithD6

end
