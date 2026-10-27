module

public import Certificates.Data.Kernel.G28.Defs
public import CFSG.Certificates.Kernel.Misc.PermG2USound
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Check

public section

namespace CFSG.KC.G28

open CFSG.RankThree.PartTwo.Sec4.Item434G28
open CFSG.KC.Misc.G2U (pk fld_pk testBit_pk blt_land bld bld_eq pk_inj pk_lt)

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem codeL_eq (m : List ℕ) : codeL m = pk 3 m := rfl

theorem fld_bit (x o m q : ℕ) : (fld x o m).testBit q = (decide (q < m) && x.testBit (o + q)) := by
  change ((x >>> o) &&& ((1 <<< m) - 1)).testBit q = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem sel_bit (a p v q : ℕ) : (sel a p v).testBit q = (a.testBit p && v.testBit q) := by
  unfold sel
  rw [blt_land]
  cases a.testBit p <;> simp

theorem lowM_lt : lowM < 2 ^ 108 := by decide +kernel

theorem highM_lt : highM < 2 ^ 108 := by decide +kernel

theorem testBit_of_lt {x q : ℕ} (hx : x < 2 ^ 108) (hq : 108 ≤ q) : x.testBit q = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hq))

theorem lowM_t0 (q : ℕ) (h : q < 36) : lowM.testBit (3 * q) = true := by
  have : ∀ q : Fin 36, lowM.testBit (3 * q.val) = true := by decide +kernel
  exact this ⟨q, h⟩

theorem lowM_t1 (q : ℕ) (h : q < 36) : lowM.testBit (3 * q + 1) = true := by
  have : ∀ q : Fin 36, lowM.testBit (3 * q.val + 1) = true := by decide +kernel
  exact this ⟨q, h⟩

theorem lowM_f (q : ℕ) : lowM.testBit (3 * q + 2) = false := by
  by_cases h : q < 36
  · have : ∀ q : Fin 36, lowM.testBit (3 * q.val + 2) = false := by decide +kernel
    exact this ⟨q, h⟩
  · exact testBit_of_lt lowM_lt (by omega)

theorem highM_t (q : ℕ) (h : q < 36) : highM.testBit (3 * q + 2) = true := by
  have : ∀ q : Fin 36, highM.testBit (3 * q.val + 2) = true := by decide +kernel
  exact this ⟨q, h⟩

theorem highM_f0 (q : ℕ) : highM.testBit (3 * q) = false := by
  by_cases h : q < 36
  · have : ∀ q : Fin 36, highM.testBit (3 * q.val) = false := by decide +kernel
    exact this ⟨q, h⟩
  · exact testBit_of_lt highM_lt (by omega)

theorem highM_f1 (q : ℕ) : highM.testBit (3 * q + 1) = false := by
  by_cases h : q < 36
  · have : ∀ q : Fin 36, highM.testBit (3 * q.val + 1) = false := by decide +kernel
    exact this ⟨q, h⟩
  · exact testBit_of_lt highM_lt (by omega)

theorem mx_bit0 (x t : ℕ) (ht : t < 36) : (mx x).testBit (3 * t) = x.testBit (3 * t + 2) := by
  change (((x &&& lowM) <<< 1) ^^^ (((x &&& highM) >>> 2) ^^^ ((x &&& highM) >>> 1))).testBit
    (3 * t) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and]
  have e1 : (decide (3 * t ≥ 1) && (x.testBit (3 * t - 1) && lowM.testBit (3 * t - 1))) =
      false := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      simp
    · have e : 3 * t - 1 = 3 * (t - 1) + 2 := by omega
      rw [e, lowM_f]
      simp
  have e2 : 2 + 3 * t = 3 * t + 2 := by omega
  have e3 : 1 + 3 * t = 3 * t + 1 := by omega
  rw [e1, e2, e3, highM_t t ht, highM_f1]
  simp

theorem mx_bit1 (x t : ℕ) (ht : t < 36) :
    (mx x).testBit (3 * t + 1) = (x.testBit (3 * t) ^^ x.testBit (3 * t + 2)) := by
  change (((x &&& lowM) <<< 1) ^^^ (((x &&& highM) >>> 2) ^^^ ((x &&& highM) >>> 1))).testBit
    (3 * t + 1) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and]
  have e1 : 3 * t + 1 - 1 = 3 * t := by omega
  have e2 : 2 + (3 * t + 1) = 3 * (t + 1) := by omega
  have e3 : 1 + (3 * t + 1) = 3 * t + 2 := by omega
  rw [e1, e2, e3, lowM_t0 t ht, highM_f0, highM_t t ht, decide_eq_true (by omega : 3 * t + 1 ≥ 1)]
  simp

theorem mx_bit2 (x t : ℕ) (ht : t < 36) :
    (mx x).testBit (3 * t + 2) = x.testBit (3 * t + 1) := by
  change (((x &&& lowM) <<< 1) ^^^ (((x &&& highM) >>> 2) ^^^ ((x &&& highM) >>> 1))).testBit
    (3 * t + 2) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and]
  have e1 : 3 * t + 2 - 1 = 3 * t + 1 := by omega
  have e2 : 2 + (3 * t + 2) = 3 * (t + 1) + 1 := by omega
  have e3 : 1 + (3 * t + 2) = 3 * (t + 1) := by omega
  rw [e1, e2, e3, lowM_t1 t ht, highM_f1, highM_f0, decide_eq_true (by omega : 3 * t + 2 ≥ 1)]
  simp

theorem mx_field (x y t : ℕ) (ht : t < 36) (h : ∀ s < 3, x.testBit (3 * t + s) = y.testBit s) :
    ∀ s < 3, (mx x).testBit (3 * t + s) = (mx y).testBit s := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  rw [Nat.add_zero] at h0
  have y0 := mx_bit0 y 0 (by omega)
  have y1 := mx_bit1 y 0 (by omega)
  have y2 := mx_bit2 y 0 (by omega)
  simp only [Nat.mul_zero, Nat.zero_add] at y0 y1 y2
  intro s hs
  interval_cases s
  · rw [Nat.add_zero, mx_bit0 x t ht, y0, h2]
  · rw [mx_bit1 x t ht, y1, h0, h2]
  · rw [mx_bit2 x t ht, y2, h1]

theorem mt_bit {c v s : ℕ} (hc : c < 8) (hv : v < 8) (hs : s < 3) :
    (mt c v).testBit s = ((c.testBit 0 && v.testBit s) ^^ ((c.testBit 1 && (mx v).testBit s) ^^
      (c.testBit 2 && (mx (mx v)).testBit s))) := by
  have : ∀ c v : Fin 8, ∀ s : Fin 3, (mt c v).testBit s =
      ((c.val.testBit 0 && v.val.testBit s) ^^ ((c.val.testBit 1 && (mx v).testBit s) ^^
        (c.val.testBit 2 && (mx (mx v)).testBit s))) := by decide +kernel
  exact this ⟨c, hc⟩ ⟨v, hv⟩ ⟨s, hs⟩

theorem getElem!_eq_toList_getD {α : Type*} [Inhabited α] (A : Array α) (n : ℕ) :
    A[n]! = A.toList.getD n default := by
  rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem getElem!_nat (A : Array ℕ) (n : ℕ) : A[n]! = A.toList.getD n 0 :=
  getElem!_eq_toList_getD A n

theorem getElem!_list (A : Array (List ℕ)) (n : ℕ) : A[n]! = A.toList.getD n [] :=
  getElem!_eq_toList_getD A n

theorem lt_of_mem {A : Array ℕ} (hA : Valid A) : ∀ x ∈ A.toList, x < 2 ^ 3 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < 36 := by
    rw [Array.length_toList, hA.1] at hi
    exact hi
  have h := hA.2 i hi'
  rw [← Array.getElem!_toList, getElem!_pos A.toList i hi] at h
  simpa using h

theorem length_toList {A : Array ℕ} (hA : Valid A) : A.toList.length = 36 := by
  rw [Array.length_toList, hA.1]

theorem codeP_bit {A : Array ℕ} (hA : Valid A) (t s : ℕ) (hs : s < 3) :
    (codeP A).testBit (3 * t + s) = (A[t]!).testBit s := by
  rw [codeP, codeL_eq, testBit_pk (lt_of_mem hA) t hs, ← getElem!_nat]

theorem codeP_lt {A : Array ℕ} (hA : Valid A) : codeP A < 2 ^ 108 := by
  have h := pk_lt (lt_of_mem hA)
  rw [length_toList hA] at h
  exact h

theorem codeP_inj {A B : Array ℕ} (hA : Valid A) (hB : Valid B) (h : codeP A = codeP B) :
    A = B :=
  Array.toList_inj.1 (pk_inj (lt_of_mem hA) (lt_of_mem hB)
    ((length_toList hA).trans (length_toList hB).symm) h)

theorem codeP_idCode : codeP idCode = idP := by decide +kernel

@[expose] noncomputable def rowT (a b0 b1 b2 i k : ℕ) : ℕ :=
  sel a (18 * i + 3 * k) (fld b0 (18 * k) 18) ^^^
    (sel a (18 * i + 3 * k + 1) (fld b1 (18 * k) 18) ^^^ sel a (18 * i + 3 * k + 2) (fld b2 (18 * k) 18))

theorem rowP_eq (a b0 b1 b2 i : ℕ) : rowP a b0 b1 b2 i =
    0 ^^^ rowT a b0 b1 b2 i 0 ^^^ rowT a b0 b1 b2 i 1 ^^^ rowT a b0 b1 b2 i 2 ^^^
      rowT a b0 b1 b2 i 3 ^^^ rowT a b0 b1 b2 i 4 ^^^ rowT a b0 b1 b2 i 5 := rfl

theorem rowT_bit {a b0 b1 b2 i k q : ℕ} (hq : q < 18) : (rowT a b0 b1 b2 i k).testBit q =
    ((a.testBit (18 * i + 3 * k) && b0.testBit (18 * k + q)) ^^
      ((a.testBit (18 * i + 3 * k + 1) && b1.testBit (18 * k + q)) ^^
        (a.testBit (18 * i + 3 * k + 2) && b2.testBit (18 * k + q)))) := by
  simp only [rowT, Nat.testBit_xor, sel_bit, fld_bit, decide_eq_true hq, Bool.true_and]

theorem rowT_hi {a b0 b1 b2 i k q : ℕ} (hq : 18 ≤ q) : (rowT a b0 b1 b2 i k).testBit q = false := by
  simp only [rowT, Nat.testBit_xor, sel_bit, fld_bit, decide_eq_false (by omega : ¬q < 18),
    Bool.false_and, Bool.and_false, Bool.xor_false]

theorem rowP_lt (a b0 b1 b2 i : ℕ) : rowP a b0 b1 b2 i < 2 ^ 18 :=
  Nat.lt_pow_two_of_testBit _ fun q hq => by
    rw [rowP_eq]
    simp only [Nat.testBit_xor, rowT_hi hq, Nat.zero_testBit, Bool.xor_false]

theorem mulQ_eq (a b0 b1 b2 : ℕ) : mulQ a b0 b1 b2 = bld 18 (rowP a b0 b1 b2) 6 := rfl

theorem rows_lt (a b0 b1 b2 : ℕ) : ∀ x ∈ (List.range 6).map (rowP a b0 b1 b2), x < 2 ^ 18 := by
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 hx
  exact rowP_lt a b0 b1 b2 k

theorem mulQ_bit {a b0 b1 b2 : ℕ} (i q : ℕ) (hi : i < 6) (hq : q < 18) :
    (mulQ a b0 b1 b2).testBit (18 * i + q) = (rowP a b0 b1 b2 i).testBit q := by
  rw [mulQ_eq, bld_eq, testBit_pk (rows_lt a b0 b1 b2) i hq,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem mulQ_lt (a b0 b1 b2 : ℕ) : mulQ a b0 b1 b2 < 2 ^ 108 := by
  have h := pk_lt (rows_lt a b0 b1 b2)
  rw [List.length_map, List.length_range] at h
  rw [mulQ_eq, bld_eq]
  exact h

theorem mulCode_get {A B : Array ℕ} {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    (mulCode A B)[6 * i + j]! = mulEntry A B i j := by
  rw [mulCode, getElem!_ofFn_nat' _ (by omega)]
  have e1 : (6 * i + j) / 6 = i := by omega
  have e2 : (6 * i + j) % 6 = j := by omega
  simp only [e1, e2]

theorem rowP_entry {A B : Array ℕ} {b0 b1 b2 i j s : ℕ} (hA : Valid A) (hB : Valid B)
    (hb0 : ∀ t < 36, ∀ s < 3, b0.testBit (3 * t + s) = (B[t]!).testBit s)
    (hb1 : ∀ t < 36, ∀ s < 3, b1.testBit (3 * t + s) = (mx B[t]!).testBit s)
    (hb2 : ∀ t < 36, ∀ s < 3, b2.testBit (3 * t + s) = (mx (mx B[t]!)).testBit s)
    (hi : i < 6) (hj : j < 6) (hs : s < 3) :
    (rowP (codeP A) b0 b1 b2 i).testBit (3 * j + s) = (mulEntry A B i j).testBit s := by
  have hT : ∀ k < 6, (rowT (codeP A) b0 b1 b2 i k).testBit (3 * j + s) =
      (mt A[6 * i + k]! B[6 * k + j]!).testBit s := by
    intro k hk
    rw [rowT_bit (by omega)]
    have e1 : 18 * i + 3 * k + 1 = 3 * (6 * i + k) + 1 := by omega
    have e2 : 18 * i + 3 * k + 2 = 3 * (6 * i + k) + 2 := by omega
    have e0 : 18 * i + 3 * k = 3 * (6 * i + k) + 0 := by omega
    have e3 : 18 * k + (3 * j + s) = 3 * (6 * k + j) + s := by omega
    rw [e1, e2, e0, e3, codeP_bit hA _ 0 (by omega), codeP_bit hA _ 1 (by omega),
      codeP_bit hA _ 2 (by omega), hb0 _ (by omega) s hs, hb1 _ (by omega) s hs,
      hb2 _ (by omega) s hs]
    exact (mt_bit (hA.2 _ (by omega)) (hB.2 _ (by omega)) hs).symm
  rw [rowP_eq]
  simp only [Nat.testBit_xor, Nat.zero_testBit, Bool.false_xor]
  rw [hT 0 (by omega), hT 1 (by omega), hT 2 (by omega), hT 3 (by omega), hT 4 (by omega),
    hT 5 (by omega), mulEntry]
  simp only [Nat.testBit_xor, Nat.add_zero, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
    Nat.reduceMul]

theorem codeP_mulCode {A B : Array ℕ} (hA : Valid A) (hB : Valid B) :
    codeP (mulCode A B) = mulP (codeP A) (codeP B) := by
  simp only [mulP, letN_eq]
  have hb0 : ∀ t < 36, ∀ s < 3, (codeP B).testBit (3 * t + s) = (B[t]!).testBit s :=
    fun t _ s hs => codeP_bit hB t s hs
  have hb1 : ∀ t < 36, ∀ s < 3, (mx (codeP B)).testBit (3 * t + s) = (mx B[t]!).testBit s :=
    fun t ht => mx_field _ _ t ht (hb0 t ht)
  have hb2 : ∀ t < 36, ∀ s < 3,
      (mx (mx (codeP B))).testBit (3 * t + s) = (mx (mx B[t]!)).testBit s :=
    fun t ht => mx_field _ _ t ht (hb1 t ht)
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 108
  · obtain ⟨i, j, s, hi, hj, hs, rfl⟩ : ∃ i j s, i < 6 ∧ j < 6 ∧ s < 3 ∧ p = 18 * i + (3 * j + s) :=
      ⟨p / 18, p % 18 / 3, p % 3, by omega, by omega, by omega, by omega⟩
    rw [mulQ_bit i _ hi (by omega), rowP_entry hA hB hb0 hb1 hb2 hi hj hs]
    have e : 18 * i + (3 * j + s) = 3 * (6 * i + j) + s := by omega
    rw [e, codeP_bit (valid_mulCode hA hB) _ s hs, mulCode_get hi hj]
  · rw [testBit_of_lt (codeP_lt (valid_mulCode hA hB)) (by omega),
      testBit_of_lt (mulQ_lt _ _ _ _) (by omega)]

theorem codeP_letterCode (n : ℕ) : codeP (letterCode n) = letterP n := by
  have h : ∀ m : Fin 96, codeP (letterCode m) = letterP m := by decide +kernel
  have e : letterCode n = letterCode (n % 96) := by
    unfold letterCode
    congr 1 <;> omega
  have e2 : letterP n = letterP (n % 96) := by
    unfold letterP
    change fld _ (Nat.mul 108 (n % 96)) 108 = fld _ (Nat.mul 108 (n % 96 % 96)) 108
    rw [Nat.mod_mod]
  rw [e, e2]
  exact h ⟨n % 96, Nat.mod_lt _ (by norm_num)⟩

theorem codeP_foldl (w : List ℕ) {A : Array ℕ} (hA : Valid A) :
    codeP (w.foldl (fun A n => mulCode A (letterCode n)) A) =
      w.foldl (fun x n => mulP x (letterP n)) (codeP A) := by
  induction w generalizing A with
  | nil => rfl
  | cons n w ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (valid_mulCode hA (valid_letterCode n)),
      codeP_mulCode hA (valid_letterCode n), codeP_letterCode]

theorem codeP_wordCode (w : List ℕ) : codeP (wordCode w) = wordP w := by
  rw [wordCode, wordP, codeP_foldl w valid_idCode, codeP_idCode]

theorem codeP_powCode {A : Array ℕ} (hA : Valid A) (k : ℕ) :
    codeP (powCode A k) = powP (codeP A) k := by
  induction k with
  | zero => exact codeP_idCode
  | succ k ih =>
    change codeP (mulCode (powCode A k) A) = mulP (powP (codeP A) k) (codeP A)
    rw [codeP_mulCode (valid_powCode hA k) hA, ih]

theorem codeP_comm {X Y : Array ℕ} (hX : Valid X) (hY : Valid Y)
    (h : mulP (codeP X) (codeP Y) = mulP (codeP Y) (codeP X)) : mulCode X Y = mulCode Y X :=
  codeP_inj (valid_mulCode hX hY) (valid_mulCode hY hX)
    (by rw [codeP_mulCode hX hY, codeP_mulCode hY hX, h])

theorem genOK_of {u z : Array ℕ} (hu : Valid u) (hz : Valid z) {gw : Array (List ℕ)}
    {tn : Array ℕ} {ts : Array (List ℕ)}
    (h : genOKP (codeP u) (codeP z) gw.toList tn.toList ts.toList = true) :
    genOK u z gw tn ts = true := by
  simp only [genOKP, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    letB_eq, Nat.blt_eq, Array.length_toList] at h
  obtain ⟨⟨⟨⟨⟨⟨hu1, hz1⟩, hsz⟩, ha⟩, hb⟩, hts⟩, hm⟩ := h
  simp only [genOK, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, Nat.eq_of_beq_eq_true hsz⟩, fun k hk => ?_⟩, fun k hk => ?_⟩,
    Nat.eq_of_beq_eq_true hts⟩, fun m hm' => ?_⟩
  · intro e
    rw [e, codeP_idCode] at hu1
    simp at hu1
  · intro e
    rw [e, codeP_idCode] at hz1
    simp at hz1
  · rw [getElem!_list]
    refine codeP_comm (valid_wordCode _) hz ?_
    rw [codeP_wordCode]
    exact Nat.eq_of_beq_eq_true (ha k hk)
  · rw [getElem!_list]
    refine codeP_comm (valid_wordCode _) hu ?_
    rw [codeP_wordCode]
    exact Nat.eq_of_beq_eq_true (hb k hk)
  · obtain ⟨h1, h2⟩ := hm m hm'
    simp only [getElem!_list, getElem!_nat]
    refine ⟨h1, codeP_inj (valid_wordCode _) (valid_letterCode _) ?_⟩
    rw [codeP_wordCode, codeP_letterCode]
    exact Nat.eq_of_beq_eq_true h2

end CFSG.KC.G28

end
