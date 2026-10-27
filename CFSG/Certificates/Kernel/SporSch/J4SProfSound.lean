
module

public import Certificates.Data.Kernel.SporSch.J4SProf
public import CFSG.Certificates.Kernel.SporSch.J4SBfsSound
public import CFSG.Sporadic.Schreier.J4SProfile
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.F4M3BSound
import CFSG.Certificates.Kernel.AS35QTS.CountSound

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.Sporadic.J4Schreier

private theorem bit_and_one (x j : Nat) :
    Nat.land (Nat.shiftRight x j) 1 = if x.testBit j then 1 else 0 := by
  have e : Nat.land (Nat.shiftRight x j) 1 = x / 2 ^ j % 2 := by
    change (x >>> j) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

private theorem par_rec (x : Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => Nat.xor s (Nat.land (Nat.shiftRight x j) (nat_lit 1))))
      n = (List.range n).foldl (fun s j => s ^^^ (if x.testBit j then 1 else 0)) 0
  | 0 => rfl
  | n + 1 => by
    change strictN _ _ = _
    rw [CFSG.KS.Raw.Orb.strictN_eq, par_rec x n, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil, bit_and_one]
    rfl

private theorem par_lt (x : Nat) : ∀ n,
    (List.range n).foldl (fun s j => s ^^^ (if x.testBit j then 1 else 0)) 0 < 2
  | 0 => by simp
  | n + 1 => by
    have h1 := par_lt x n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun s j => s ^^^ (if x.testBit j then 1 else 0)) 0 = a at h1 ⊢
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> cases x.testBit n <;> decide

private theorem ellK_eq (a : Nat) : ellK a = ell a := by
  unfold ellK par11 ell
  exact par_rec _ 11

private theorem ell_le (n : Nat) : ell n ≤ 1 := by
  have := par_lt (n &&& 300) 11
  unfold ell
  omega

private noncomputable def kR (E SQ : Nat → Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ _ => 5)
    (fun _ ih n e m => Bool.rec (motive := fun _ => Nat)
      (strictN (Nat.xor n (appK (E e) n)) (fun n' => ih n' (SQ e) (Nat.succ m))) m
      (Bool.rec (motive := fun _ => Bool) false (Nat.beq e 0) (Nat.beq n 0)))

private theorem kfunK_eq_kR (E SQ : Nat → Nat) (n e : Nat) : kfunK E SQ n e = kR E SQ 5 n e 0 :=
  rfl

private theorem kR_succ (E SQ : Nat → Nat) (k n e m : Nat) :
    kR E SQ (k + 1) n e m =
      if n = 0 ∧ e = 0 then m else kR E SQ k (n ^^^ appK (E e) n) (SQ e) (m + 1) := by
  change Bool.rec (motive := fun _ => Nat)
    (strictN (Nat.xor n (appK (E e) n)) (fun n' => kR E SQ k n' (SQ e) (Nat.succ m))) m
    (Bool.rec (motive := fun _ => Bool) false (Nat.beq e 0) (Nat.beq n 0)) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq]
  by_cases h : n = 0 ∧ e = 0
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · rw [if_neg h]
    have hb : Bool.rec (motive := fun _ => Bool) false (Nat.beq e 0) (Nat.beq n 0) = false := by
      rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_false_iff]
      by_cases hn : n = 0
      · exact Or.inr (Bool.eq_false_iff.2 fun h' => h ⟨hn, Nat.eq_of_beq_eq_true h'⟩)
      · exact Or.inl (Bool.eq_false_iff.2 fun h' => hn (Nat.eq_of_beq_eq_true h'))
    rw [hb]
    rfl

private theorem find_succ (p : ℕ × ℕ) (k : ℕ) :
    (List.range (k + 1)).find? (fun m => stepNF^[m] p == (0, 0)) =
      if p = (0, 0) then some 0
      else ((List.range k).find? (fun m => stepNF^[m] (stepNF p) == (0, 0))).map Nat.succ := by
  rw [List.range_succ_eq_map, List.find?_cons]
  by_cases hp : p = (0, 0)
  · rw [if_pos hp]
    simp [hp]
  · rw [if_neg hp]
    have h0 : (stepNF^[0] p == (0, 0)) = false := by simpa using hp
    simp only [h0, List.find?_map, Function.comp_def, Function.iterate_succ_apply]

private theorem kR_spec {E SQ : Nat → Nat} (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e))
    (hSQ : squares = tabA 1024 SQ) (hSQb : ∀ e < 1024, SQ e < 1024) :
    ∀ (k n e m : Nat), e < 1024 → kR E SQ k n e m =
      ((List.range k).find? (fun i => stepNF^[i] (n, e) == (0, 0))).elim 5 (fun i => m + i)
  | 0, _, _, _, _ => rfl
  | k + 1, n, e, m, he => by
    have hstep : stepNF (n, e) = (n ^^^ appK (E e) n, SQ e) := by
      unfold stepNF
      dsimp only
      rw [hE e he, app_eq, hSQ, tabA_get he]
    rw [kR_succ, find_succ, hstep]
    by_cases h : n = 0 ∧ e = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · have hp : (n, e) ≠ (0, 0) := fun e' => h (Prod.mk.inj e')
      rw [if_neg h, if_neg hp, kR_spec hE hSQ hSQb k _ _ (m + 1) (hSQb e he)]
      cases ((List.range k).find? (fun i => stepNF^[i] (n ^^^ appK (E e) n, SQ e) == (0, 0))) with
      | none => rfl
      | some i =>
        show m + 1 + i = m + Nat.succ i
        omega

private theorem kfunK_eq {E SQ : Nat → Nat} (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e))
    (hSQ : squares = tabA 1024 SQ) (hSQb : ∀ e < 1024, SQ e < 1024) {n e : Nat} (he : e < 1024) :
    kfunK E SQ n e = kfun n e := by
  rw [kfunK_eq_kR, kR_spec hE hSQ hSQb 5 n e 0 he, kfun]
  cases ((List.range 5).find? (fun i => stepNF^[i] (n, e) == (0, 0))) with
  | none => rfl
  | some i =>
    show 0 + i = i
    omega

private theorem kfun_le (n e : Nat) : kfun n e ≤ 5 := by
  unfold kfun
  cases h : (List.range 5).find? (fun m => stepNF^[m] (n, e) == (0, 0)) with
  | none => simp
  | some i =>
    have := List.mem_range.1 (List.mem_of_find?_eq_some h)
    simp only [Option.getD_some]
    omega

private theorem foldr_add (g : Nat → Nat) : ∀ (n s : Nat),
    (List.range n).foldr (fun i s => Nat.add s (g i)) s = s + ∑ i ∈ Finset.range n, g i
  | 0, s => by simp
  | n + 1, s => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_add g n,
      Finset.sum_range_succ]
    show s + g n + _ = _
    omega

private theorem foldN_add (g : Nat → Nat) (n : Nat) :
    foldN n (fun i s => Nat.add s (g i)) 0 = ∑ i ∈ Finset.range n, g i := by
  rw [CFSG.KS.Raw.Orb.foldN_eq, foldr_add, Nat.zero_add]

private theorem shl_one (x : Nat) : Nat.shiftLeft 1 x = 2 ^ x := Nat.one_shiftLeft x

private def idx (CT : Nat → Nat) (n e : Nat) : Nat := 6 * (ell n + 2 * CT e) + kfun n e

private theorem cntE_eq {E SQ CT : Nat → Nat}
    (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e)) (hSQ : squares = tabA 1024 SQ)
    (hSQb : ∀ e < 1024, SQ e < 1024) {e : Nat} (he : e < 1024) :
    cntE E SQ CT e = ∑ n ∈ Finset.range 2048, 2 ^ (24 * idx CT n e) := by
  unfold cntE
  simp only [CFSG.KS.Raw.Orb.strictN_eq]
  rw [foldN_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [shl_one, ellK_eq, kfunK_eq hE hSQ hSQb he]
  rfl

private def bx (g : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => bx g k ^^ g k

private def bo (g : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => bo g k || g k

private theorem bx_congr {g g' : ℕ → Bool} : ∀ {k}, (∀ j < k, g j = g' j) → bx g k = bx g' k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [bx]
    rw [bx_congr fun j hj => h j (by omega), h k (by omega)]

private theorem bo_congr {g g' : ℕ → Bool} : ∀ {k}, (∀ j < k, g j = g' j) → bo g k = bo g' k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [bo]
    rw [bo_congr fun j hj => h j (by omega), h k (by omega)]

private theorem bx_false {g : ℕ → Bool} : ∀ {k}, (∀ j < k, g j = false) → bx g k = false
  | 0, _ => rfl
  | k + 1, h => by
    simp only [bx]
    rw [bx_false fun j hj => h j (by omega), h k (by omega)]
    rfl

private theorem bo_iff (g : ℕ → Bool) : ∀ k, bo g k = true ↔ ∃ j < k, g j = true
  | 0 => by simp [bo]
  | k + 1 => by
    simp only [bo, Bool.or_eq_true, bo_iff g k]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr h

private theorem bit_beq (a j : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight a j) 1) 1 = a.testBit j := by
  rw [bit_and_one]
  cases a.testBit j <;> rfl

private abbrev Lo (x : ℕ) : Prop := ∀ i, 2048 ≤ i → x.testBit i = false

private abbrev Rep (V : ℕ) (x : ℕ → ℕ) : Prop :=
  ∀ n < 2048, ∀ r < 11, (plB V r).testBit n = (x n).testBit r

private abbrev Hi (x : ℕ → ℕ) : Prop := ∀ n < 2048, ∀ i, 11 ≤ i → (x n).testBit i = false

private theorem mask_bit (W i : ℕ) : (Nat.sub (Nat.shiftLeft 1 W) 1).testBit i = decide (i < W) := by
  change ((1 <<< W) - 1).testBit i = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]

private theorem plB_bit (V r : ℕ) {n : ℕ} (hn : n < 2048) :
    (plB V r).testBit n = V.testBit (2048 * r + n) := by
  change ((V >>> (2048 * r)) &&& Nat.sub (Nat.shiftLeft 1 2048) 1).testBit n = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, mask_bit, decide_eq_true hn, Bool.and_true]

private theorem plB_lo (V r : ℕ) : Lo (plB V r) := by
  intro i hi
  change ((V >>> (2048 * r)) &&& Nat.sub (Nat.shiftLeft 1 2048) 1).testBit i = false
  rw [Nat.testBit_and, mask_bit, decide_eq_false (by omega), Bool.and_false]

private theorem lo_xor {a b : ℕ} (ha : Lo a) (hb : Lo b) : Lo (a ^^^ b) := by
  intro i hi
  rw [Nat.testBit_xor, ha i hi, hb i hi]
  rfl

private noncomputable def pR (Q : ℕ → ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun r acc => strictN acc (fun s => Nat.lor s (Nat.shiftLeft (Q r) (Nat.mul (nat_lit 2048) r))))

private theorem pR_succ (Q : ℕ → ℕ) (k : ℕ) :
    pR Q (k + 1) = pR Q k ||| (Q k <<< (2048 * k)) := by
  change strictN (pR Q k)
    (fun s => Nat.lor s (Nat.shiftLeft (Q k) (Nat.mul (nat_lit 2048) k))) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq]
  rfl

private theorem pR_bit (Q : ℕ → ℕ) (hQ : ∀ r, Lo (Q r)) {n : ℕ} (hn : n < 2048) :
    ∀ k r, (pR Q k).testBit (2048 * r + n) = (decide (r < k) && (Q r).testBit n)
  | 0, r => by
    change (0 : ℕ).testBit _ = _
    simp
  | k + 1, r => by
    rw [pR_succ, Nat.testBit_or, pR_bit Q hQ hn k r, Nat.testBit_shiftLeft]
    rcases lt_trichotomy r k with h | rfl | h
    · rw [decide_eq_false (show ¬ 2048 * r + n ≥ 2048 * k by omega)]
      simp [h, show r < k + 1 by omega]
    · simp
    · rw [hQ k (2048 * r + n - 2048 * k) (by omega)]
      simp [show ¬ r < k by omega, show ¬ r < k + 1 by omega]

private theorem plB_pack (Q : ℕ → ℕ) (hQ : ∀ r, Lo (Q r)) {r n : ℕ} (hr : r < 11)
    (hn : n < 2048) : (plB (packB Q) r).testBit n = (Q r).testBit n := by
  rw [plB_bit _ _ hn]
  change (pR Q 11).testBit _ = _
  rw [pR_bit Q hQ hn, decide_eq_true hr, Bool.true_and]

private noncomputable def sR (V : ℕ) (f : ℕ → Bool) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun j acc => strictN acc (fun s => nIf(f j, Nat.xor s (plB V j), s)))

private theorem sR_succ (V : ℕ) (f : ℕ → Bool) (k : ℕ) :
    sR V f (k + 1) = if f k then sR V f k ^^^ plB V k else sR V f k := by
  change strictN (sR V f k) (fun s => nIf(f k, Nat.xor s (plB V k), s)) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq]
  cases f k <;> rfl

private theorem sR_bit {V : ℕ} {f : ℕ → Bool} {n x : ℕ}
    (hx : ∀ j < 11, (plB V j).testBit n = x.testBit j) :
    ∀ k, k ≤ 11 → (sR V f k).testBit n = bx (fun j => f j && x.testBit j) k
  | 0, _ => by
    change (0 : ℕ).testBit _ = _
    simp [bx]
  | k + 1, hk => by
    rw [sR_succ]
    simp only [bx]
    rw [← sR_bit hx k (by omega)]
    cases f k
    · simp
    · simp [Nat.testBit_xor, hx k (by omega)]

private theorem sR_lo (V : ℕ) (f : ℕ → Bool) : ∀ k, Lo (sR V f k)
  | 0 => fun i _ => Nat.zero_testBit i
  | k + 1 => by
    rw [sR_succ]
    cases f k
    · exact sR_lo V f k
    · exact lo_xor (sR_lo V f k) (plB_lo V k)

private noncomputable def aR (P a : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun j acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1))
      (nat_lit 1), Nat.xor s (colK P j), s)))

private theorem aR_succ (P a k : ℕ) :
    aR P a (k + 1) = if a.testBit k then aR P a k ^^^ colK P k else aR P a k := by
  change strictN (aR P a k) (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a k) (nat_lit 1))
    (nat_lit 1), Nat.xor s (colK P k), s)) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq, bit_beq]
  cases a.testBit k <;> rfl

private theorem aR_bit (P a r : ℕ) : ∀ k,
    (aR P a k).testBit r = bx (fun j => a.testBit j && (colK P j).testBit r) k
  | 0 => by
    change (0 : ℕ).testBit _ = _
    simp [bx]
  | k + 1 => by
    rw [aR_succ]
    simp only [bx]
    rw [← aR_bit P a r k]
    cases a.testBit k
    · simp
    · simp [Nat.testBit_xor]

private theorem appK_bit (P a r : ℕ) :
    (appK P a).testBit r = bx (fun j => a.testBit j && (colK P j).testBit r) 11 :=
  aR_bit P a r 11

private theorem colK_hi (P j : ℕ) {i : ℕ} (hi : 11 ≤ i) : (colK P j).testBit i = false := by
  change ((P >>> (11 * j)) &&& 2047).testBit i = false
  rw [Nat.testBit_and, Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : (2047 : ℕ) < 2 ^ 11)
    (Nat.pow_le_pow_right (by norm_num) hi)), Bool.and_false]

private theorem step_rep {P V : ℕ} {x : ℕ → ℕ} (hV : Rep V x) :
    Rep (stepB P V) (fun n => x n ^^^ appK P (x n)) := by
  intro n hn r hr
  have hQ : ∀ r, Lo ((fun r => Nat.xor (plB V r) (selB V (fun j =>
      Nat.beq (Nat.land (Nat.shiftRight (colK P j) r) 1) 1))) r) := fun r =>
    lo_xor (plB_lo V r) (sR_lo V (fun j => Nat.beq (Nat.land (Nat.shiftRight (colK P j) r) 1) 1) 11)
  change (plB (packB _) r).testBit n = _
  rw [plB_pack _ hQ hr hn]
  change (plB V r ^^^ sR V (fun j => Nat.beq (Nat.land (Nat.shiftRight (colK P j) r) 1) 1)
    11).testBit n = (x n ^^^ appK P (x n)).testBit r
  rw [Nat.testBit_xor, Nat.testBit_xor, hV n hn r hr, appK_bit, sR_bit (hV n hn) 11 le_rfl]
  congr 1
  refine bx_congr fun j _ => ?_
  rw [bit_beq, Bool.and_comm]

private theorem step_hi {P : ℕ} {x : ℕ → ℕ} (hx : Hi x) : Hi (fun n => x n ^^^ appK P (x n)) := by
  intro n hn i hi
  change (x n ^^^ appK P (x n)).testBit i = false
  rw [Nat.testBit_xor, hx n hn i hi, appK_bit,
    bx_false fun j _ => by rw [colK_hi P j hi, Bool.and_false]]
  rfl

private noncomputable def oR (V : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun r acc => strictN acc (fun s => Nat.lor s (plB V r)))

private theorem oR_bit (V n : ℕ) : ∀ k, (oR V k).testBit n = bo (fun r => (plB V r).testBit n) k
  | 0 => by
    change (0 : ℕ).testBit _ = _
    simp [bo]
  | k + 1 => by
    change (strictN (oR V k) (fun s => Nat.lor s (plB V k))).testBit n = _
    rw [CFSG.KS.Raw.Orb.strictN_eq]
    change (oR V k ||| plB V k).testBit n = _
    rw [Nat.testBit_or, oR_bit V n k]
    rfl

private theorem nzB_bit {V : ℕ} {x : ℕ → ℕ} (hV : Rep V x) (hx : Hi x) {n : ℕ} (hn : n < 2048) :
    (nzB V).testBit n = decide (x n ≠ 0) := by
  change (oR V 11).testBit n = _
  rw [oR_bit, bo_congr (g' := fun r => (x n).testBit r) fun r hr => hV n hn r hr,
    Bool.eq_iff_iff, decide_eq_true_iff, bo_iff]
  constructor
  · rintro ⟨r, _, h⟩ h0
    rw [h0, Nat.zero_testBit] at h
    exact Bool.false_ne_true h
  · intro h0
    by_contra hne
    simp only [not_exists, not_and] at hne
    refine h0 (Nat.eq_of_testBit_eq fun i => ?_)
    rw [Nat.zero_testBit]
    by_cases hi : i < 11
    · simpa using hne i hi
    · exact hx n hn i (by omega)

private theorem divmod_bit (x j : ℕ) : x / 2 ^ j % 2 = if x.testBit j then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

private theorem pc_eq (x : ℕ) :
    CFSG.KC.popcount x 2048 = ∑ n ∈ Finset.range 2048, if x.testBit n then 1 else 0 :=
  (CFSG.KC.AS35QTS.popcount_sum x 63 (by norm_num)).trans
    (Finset.sum_congr rfl fun j _ => divmod_bit x j)

private theorem cntZ_eq {L : ℕ} (hL : ∀ n < 2048, L.testBit n = decide (ellK n = 1)) (c Z f : ℕ) :
    cntZ c L Z f = ∑ n ∈ Finset.range 2048,
      if Z.testBit n then 2 ^ (24 * (6 * (ellK n + 2 * c) + f)) else 0 := by
  unfold cntZ
  by_cases hZ : Z = 0
  · subst hZ
    change (0 : ℕ) = _
    simp
  · rw [show Nat.beq Z 0 = false from Bool.eq_false_iff.2 fun h => hZ (Nat.eq_of_beq_eq_true h)]
    simp only [CFSG.KS.Raw.Orb.strictN_eq]
    change CFSG.KC.popcount (Z &&& L) 2048 <<< (24 * (6 * (1 + 2 * c) + f)) +
        CFSG.KC.popcount (Z ^^^ (Z &&& L)) 2048 <<< (24 * (6 * (0 + 2 * c) + f)) = _
    rw [pc_eq, pc_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Nat.testBit_xor, Nat.testBit_and, hL n (Finset.mem_range.1 hn)]
    have h1 := ell_le n
    rw [← ellK_eq] at h1
    rcases (by omega : ellK n = 0 ∨ ellK n = 1) with h | h <;> cases Z.testBit n <;> simp [h]

private theorem loopB_succ (E SQ : ℕ → ℕ) (c L k V e D m : ℕ) :
    loopB E SQ c L (k + 1) V e D m =
      if D = 0 then 0 else
        cntZ c L (if e = 0 then D ^^^ (D &&& nzB V) else 0) m +
          loopB E SQ c L k (stepB (E e) V) (SQ e)
            (D ^^^ (if e = 0 then D ^^^ (D &&& nzB V) else 0)) (m + 1) := by
  change Bool.rec (motive := fun _ => ℕ) (strictN V (fun V' =>
      strictN (Bool.rec (motive := fun _ => ℕ) 0 (Nat.xor D (Nat.land D (nzB V'))) (Nat.beq e 0))
        (fun Z => Nat.add (cntZ c L Z m)
          (loopB E SQ c L k (stepB (E e) V') (SQ e) (Nat.xor D Z) (Nat.succ m))))) 0
      (Nat.beq D 0) = _
  simp only [CFSG.KS.Raw.Orb.strictN_eq]
  by_cases hD : D = 0
  · subst hD
    rfl
  · rw [if_neg hD,
      show Nat.beq D 0 = false from Bool.eq_false_iff.2 fun h => hD (Nat.eq_of_beq_eq_true h)]
    by_cases he : e = 0
    · subst he
      rfl
    · rw [if_neg he,
        show Nat.beq e 0 = false from Bool.eq_false_iff.2 fun h => he (Nat.eq_of_beq_eq_true h)]
      rfl

private theorem loopB_spec {E SQ : ℕ → ℕ} {c L : ℕ}
    (hL : ∀ n < 2048, L.testBit n = decide (ellK n = 1)) :
    ∀ (k V e D m : ℕ) (x : ℕ → ℕ), Rep V x → Hi x →
      loopB E SQ c L k V e D m = ∑ n ∈ Finset.range 2048,
        if D.testBit n then 2 ^ (24 * (6 * (ellK n + 2 * c) + kR E SQ k (x n) e m)) else 0
  | 0, V, e, D, m, x, _, _ => by
    change cntZ c L D 5 = _
    rw [cntZ_eq hL]
    rfl
  | k + 1, V, e, D, m, x, hV, hx => by
    rw [loopB_succ]
    by_cases hD : D = 0
    · subst hD
      simp
    · rw [if_neg hD, cntZ_eq hL, loopB_spec hL k _ _ _ _ _ (step_rep hV) (step_hi hx),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hz := nzB_bit hV hx (Finset.mem_range.1 hn)
      rw [kR_succ]
      by_cases he : e = 0
      · subst he
        simp only [if_true, Nat.testBit_xor, Nat.testBit_and, hz]
        by_cases h0 : x n = 0 <;> cases D.testBit n <;> simp [h0]
      · simp only [if_neg he, Nat.zero_testBit, Nat.xor_zero]
        cases D.testBit n <;> simp [he]

private theorem idB_rep : Rep idB (fun n => n) := by
  intro n hn r hr
  have hQ : ∀ r, Lo ((fun r => CFSG.KC.F4M3B.pln r 11) r) := fun r i hi => by
    rw [CFSG.KC.F4M3B.pln_bit, decide_eq_false (Nat.not_lt.2 (le_trans (by norm_num) hi)),
      Bool.false_and]
  change (plB (packB _) r).testBit n = _
  rw [plB_pack _ hQ hr hn, CFSG.KC.F4M3B.pln_bit,
    decide_eq_true (lt_of_lt_of_le hn (by norm_num)), Bool.true_and]

private theorem idB_hi : Hi (fun n => n) := fun n hn i hi =>
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (le_trans (by norm_num) (Nat.pow_le_pow_right
    (by norm_num) hi)))

private theorem xor_ite : ∀ b c : Bool,
    Nat.xor (if b then 1 else 0) (if c then 1 else 0) = if (b ^^ c) then 1 else 0 := by
  decide

private theorem par_bx (a : ℕ) : ∀ k, Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun j acc => strictN acc (fun s => Nat.xor s (Nat.land (Nat.shiftRight a j) (nat_lit 1)))) k =
    if bx (fun j => a.testBit j) k then 1 else 0
  | 0 => rfl
  | k + 1 => by
    change strictN (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun j acc => strictN acc (fun s => Nat.xor s (Nat.land (Nat.shiftRight a j) (nat_lit 1)))) k)
      (fun s => Nat.xor s (Nat.land (Nat.shiftRight a k) (nat_lit 1))) = _
    rw [CFSG.KS.Raw.Orb.strictN_eq, par_bx a k, bit_and_one, xor_ite]
    rfl

private theorem ellB_bit {n : ℕ} (hn : n < 2048) : ellB.testBit n = decide (ellK n = 1) := by
  change (sR idB (fun j => Nat.beq (Nat.land (Nat.shiftRight 300 j) 1) 1) 11).testBit n = _
  rw [sR_bit (idB_rep n hn) 11 le_rfl]
  change bx (fun j => Nat.beq (Nat.land (Nat.shiftRight 300 j) 1) 1 && n.testBit j) 11 =
    decide (par11 (n &&& 300) = 1)
  rw [show par11 (n &&& 300) = if bx (fun j => (n &&& 300).testBit j) 11 then 1 else 0 from
    par_bx (n &&& 300) 11]
  have e : bx (fun j => Nat.beq (Nat.land (Nat.shiftRight 300 j) 1) 1 && n.testBit j) 11 =
      bx (fun j => (n &&& 300).testBit j) 11 :=
    bx_congr fun j _ => by rw [bit_beq, Nat.testBit_and, Bool.and_comm]
  rw [e]
  cases bx (fun j => (n &&& 300).testBit j) 11 <;> rfl

private theorem cntB_eq {E SQ CT : Nat → Nat}
    (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e)) (hSQ : squares = tabA 1024 SQ)
    (hSQb : ∀ e < 1024, SQ e < 1024) {e : Nat} (he : e < 1024) :
    cntB E SQ CT e = cntE E SQ CT e := by
  rw [cntE_eq hE hSQ hSQb he]
  unfold cntB
  simp only [CFSG.KS.Raw.Orb.strictN_eq]
  rw [loopB_spec (fun n hn => ellB_bit hn) 5 idB e _ 0 (fun n => n) idB_rep idB_hi]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hD : (Nat.sub (Nat.shiftLeft 1 2048) 1).testBit n = true := by
    rw [mask_bit, decide_eq_true (Finset.mem_range.1 hn)]
  rw [hD, if_pos rfl, ← kfunK_eq_kR, kfunK_eq hE hSQ hSQb he, ellK_eq]
  rfl

private theorem sliceB_eq (E SQ CT : Nat → Nat) (s : Nat) :
    sliceB E SQ CT s = ∑ d ∈ Finset.range 8, cntB E SQ CT (8 * s + d) := by
  unfold sliceB
  rw [foldN_add]
  rfl

private theorem sumK_eq (S : Nat → Nat) (k : Nat) : sumK S k = ∑ s ∈ Finset.range k, S s := by
  unfold sumK
  exact foldN_add S k

private theorem sum_blocks (f : ℕ → ℕ) : ∀ k,
    ∑ s ∈ Finset.range k, ∑ d ∈ Finset.range 8, f (8 * s + d) = ∑ e ∈ Finset.range (8 * k), f e
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, sum_blocks f k, show 8 * (k + 1) = 8 * k + 8 by ring,
      Finset.sum_range_add]

private theorem total_eq {E SQ CT S : Nat → Nat}
    (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e)) (hSQ : squares = tabA 1024 SQ)
    (hSQb : ∀ e < 1024, SQ e < 1024) (hs : ∀ s < 128, Nat.beq (sliceB E SQ CT s) (S s) = true) :
    sumK S 128 = ∑ e ∈ Finset.range 1024, ∑ n ∈ Finset.range 2048, 2 ^ (24 * idx CT n e) := by
  rw [sumK_eq, Finset.sum_congr rfl fun s hs' =>
    (Nat.eq_of_beq_eq_true (hs s (Finset.mem_range.1 hs'))).symm]
  simp only [sliceB_eq]
  rw [sum_blocks (fun e => cntB E SQ CT e) 128]
  exact Finset.sum_congr (by norm_num) fun e he => by
    have he' : e < 1024 := by simpa using Finset.mem_range.1 he
    rw [cntB_eq hE hSQ hSQb he', cntE_eq hE hSQ hSQb he']

private theorem low_lt {B : ℕ} (c : ℕ → ℕ) (hc : ∀ f, c f < B) : ∀ g,
    ∑ f ∈ Finset.range g, c f * B ^ f < B ^ g
  | 0 => by simp
  | g + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := low_lt c hc g
    have h2 : c g + 1 ≤ B := hc g
    calc ∑ f ∈ Finset.range g, c f * B ^ f + c g * B ^ g < B ^ g + c g * B ^ g := by omega
      _ = (c g + 1) * B ^ g := by ring
      _ ≤ B * B ^ g := Nat.mul_le_mul_right _ h2
      _ = B ^ g * B := by ring

private theorem digit_eq {B : ℕ} (hB : 0 < B) (c : ℕ → ℕ) (hc : ∀ f, c f < B) : ∀ F g, g < F →
    (∑ f ∈ Finset.range F, c f * B ^ f) / B ^ g % B = c g
  | 0, g, h => absurd h (Nat.not_lt_zero g)
  | F + 1, g, h => by
    rw [Finset.sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with hg | rfl
    · have e : c F * B ^ F = (c F * B ^ (F - g - 1) * B) * B ^ g := by
        rw [mul_assoc (c F * B ^ (F - g - 1)), mul_assoc, ← pow_succ', ← pow_add,
          show F - g - 1 + (g + 1) = F by omega]
      rw [e, Nat.add_mul_div_right _ _ (pow_pos hB g), Nat.add_mul_mod_self_right]
      exact digit_eq hB c hc F g hg
    · rw [Nat.add_mul_div_right _ _ (pow_pos hB _), Nat.div_eq_of_lt (low_lt c hc _),
        Nat.zero_add, Nat.mod_eq_of_lt (hc _)]

private theorem ent_eq (w P i : Nat) : ent w P i = P / 2 ^ (w * i) % 2 ^ w :=
  CFSG.KS.Raw.Orb.pg_eq w P i

theorem prof_sound {E SQ CT S PTB : Nat → Nat}
    (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e))
    (hSQ : squares = tabA 1024 SQ) (hSQb : ∀ e < 1024, SQ e < 1024)
    (hCT : cTable = tabA 1024 CT) (hCTb : ∀ e < 1024, CT e < 16)
    (hs : ∀ s < 128, Nat.beq (sliceB E SQ CT s) (S s) = true)
    (ht : profK PTB (sumK S 128) = true) :
    (∀ e < 1024, ∀ n < 2048, kfun n e < 5) ∧
      ∀ b < 32, ∀ j < 5, profCount b j = ent 24 (PTB b) j := by
  set c : ℕ → ℕ := fun f => ∑ e ∈ Finset.range 1024, ∑ n ∈ Finset.range 2048,
    if idx CT n e = f then 1 else 0 with hc
  have hidx : ∀ e < 1024, ∀ n, idx CT n e < 192 := by
    intro e he n
    have h1 := ell_le n
    have h2 := hCTb e he
    have h3 := kfun_le n e
    unfold idx
    omega
  have hcle : ∀ f, c f < 2 ^ 24 := by
    intro f
    have : c f ≤ 1024 * 2048 := by
      calc c f ≤ ∑ e ∈ Finset.range 1024, ∑ n ∈ Finset.range 2048, 1 := by
            refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun n _ => ?_
            split <;> simp
        _ = 1024 * 2048 := by simp
    exact lt_of_le_of_lt this (by norm_num)
  have htot : sumK S 128 = ∑ f ∈ Finset.range 192, c f * (2 ^ 24) ^ f := by
    rw [total_eq hE hSQ hSQb hs]
    have hterm : ∀ e < 1024, ∀ n, 2 ^ (24 * idx CT n e) =
        ∑ f ∈ Finset.range 192, (if idx CT n e = f then 1 else 0) * (2 ^ 24) ^ f := by
      intro e he n
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (hidx e he n)), ← pow_mul]
    rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun n _ =>
      hterm e (Finset.mem_range.1 he) n]
    rw [Finset.sum_congr rfl fun e _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [hc, Finset.sum_mul]
  have hfield : ∀ f < 192, ent 24 (sumK S 128) f = c f := by
    intro f hf
    rw [ent_eq, htot, pow_mul]
    exact digit_eq (by positivity) c hcle 192 f hf
  unfold profK at ht
  have hprof : ∀ b < 32, (∀ j < 5, ent 24 (sumK S 128) (6 * b + j) = ent 24 (PTB b) j) ∧
      ent 24 (sumK S 128) (6 * b + 5) = 0 := by
    intro b hb
    have h := CFSG.KS.allN_spec ht b hb
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨fun j hj => Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h1 j hj),
      Nat.eq_of_beq_eq_true h2⟩
  refine ⟨fun e he n hn => ?_, fun b hb j hj => ?_⟩
  ·
    by_contra hk
    have h5 : kfun n e = 5 := by have := kfun_le n e; omega
    have hb32 : ell n + 2 * CT e < 32 := by
      have := ell_le n
      have := hCTb e he
      omega
    have hc0 : c (6 * (ell n + 2 * CT e) + 5) = 0 := by
      rw [← hfield (6 * (ell n + 2 * CT e) + 5) (by omega)]
      exact (hprof _ hb32).2
    have hpos : 1 ≤ c (6 * (ell n + 2 * CT e) + 5) := by
      simp only [hc]
      have hi : idx CT n e = 6 * (ell n + 2 * CT e) + 5 := by
        unfold idx
        omega
      calc 1 = (if idx CT n e = 6 * (ell n + 2 * CT e) + 5 then 1 else 0) := by rw [if_pos hi]
        _ ≤ ∑ n' ∈ Finset.range 2048,
              (if idx CT n' e = 6 * (ell n + 2 * CT e) + 5 then 1 else 0) :=
          Finset.single_le_sum (f := fun n' =>
            if idx CT n' e = 6 * (ell n + 2 * CT e) + 5 then 1 else 0) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.2 hn)
        _ ≤ ∑ e' ∈ Finset.range 1024, ∑ n' ∈ Finset.range 2048,
              (if idx CT n' e' = 6 * (ell n + 2 * CT e) + 5 then 1 else 0) :=
          Finset.single_le_sum (f := fun e' => ∑ n' ∈ Finset.range 2048,
            (if idx CT n' e' = 6 * (ell n + 2 * CT e) + 5 then 1 else 0)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.2 he)
    omega
  ·
    rw [← (hprof b hb).1 j hj, hfield (6 * b + j) (by omega)]
    simp only [hc]
    unfold profCount
    rw [Fin.sum_univ_eq_sum_range (fun e => if cTable[e]! = b / 2 then
      ((Finset.univ : Finset (Fin 2048)).filter fun n => ell n.val = b % 2 ∧ kfun n.val e = j).card
      else 0) 1024]
    refine Finset.sum_congr rfl fun e he => ?_
    have he' := Finset.mem_range.1 he
    rw [hCT, tabA_get he', Finset.card_filter,
      Fin.sum_univ_eq_sum_range (fun n => if ell n = b % 2 ∧ kfun n e = j then 1 else 0) 2048]
    by_cases hce : CT e = b / 2
    · rw [if_pos hce]
      refine Finset.sum_congr rfl fun n _ => ?_
      have h1 := ell_le n
      have h3 := kfun_le n e
      by_cases hp : ell n = b % 2 ∧ kfun n e = j
      · rw [if_pos hp, if_pos (show idx CT n e = 6 * b + j by unfold idx; omega)]
      · rw [if_neg hp, if_neg (show ¬ idx CT n e = 6 * b + j by unfold idx; omega)]
    · rw [if_neg hce]
      symm
      refine Finset.sum_eq_zero fun n _ => ?_
      have h1 := ell_le n
      have h3 := kfun_le n e
      rw [if_neg (show ¬ idx CT n e = 6 * b + j by unfold idx; omega)]

end CFSG.KS.SporSch.C11

end
