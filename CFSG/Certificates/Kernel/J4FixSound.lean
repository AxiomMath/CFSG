module

public import Certificates.Data.Kernel.J4FixK
public import CFSG.Certificates.Kernel.OpsKSound
import all CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.Co1BTrSound

set_option maxRecDepth 400000

public section

namespace CFSG.KC.J4Fix

open CFSG.KC.M1F2 CFSG.SectionRank.Native CFSG.Quasithin.H13.NQCat.Native
open CFSG.Sporadic.SmallF2.Native
open CFSG.KC.Co1F2 (unpackR)
open CFSG.KLie.CT (bit)

private theorem testBit_innerT (d i r : Nat) (hi : i < d) : ∀ (n acc q : Nat),
    ((List.range n).foldl (fun acc j => if r.testBit j then acc ||| (1 <<< (d * j + i)) else acc)
      acc).testBit q =
      (acc.testBit q || (decide (q % d = i) && decide (q / d < n) && r.testBit (q / d)))
  | 0, acc, q => by simp
  | n + 1, acc, q => by
    have hq : d * n + i = q ↔ q % d = i ∧ q / d = n := by
      constructor
      · rintro rfl
        refine ⟨?_, ?_⟩
        · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
        · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
      · rintro ⟨h1, h2⟩
        rw [← h1, ← h2, Nat.div_add_mod]
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := testBit_innerT d i r hi n acc q
    by_cases h2 : q / d = n
    · have hd : (d * n + i = q) ↔ q % d = i := by rw [hq, h2]; simp
      by_cases hr : r.testBit n
      · rw [if_pos hr, Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow, h2, hr]
        simp [hd]
      · rw [if_neg hr, ih, h2]
        simp [hr]
    · have hd : ¬ (d * n + i = q) := fun e => h2 (hq.1 e).2
      have hlt : (q / d < n + 1) ↔ (q / d < n) := by omega
      by_cases hr : r.testBit n
      · rw [if_pos hr, Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
        simp [hd, hlt]
      · rw [if_neg hr, ih]
        simp [hlt]

private theorem testBit_transF_aux (d X : Nat) : ∀ (m q : Nat), m ≤ d →
    ((List.range m).foldl (fun acc i =>
      (List.range d).foldl (fun acc j =>
        if (rowF d X i).testBit j then acc ||| (1 <<< (d * j + i)) else acc) acc) 0).testBit q =
      (decide (q % d < m) && decide (q / d < d) && (rowF d X (q % d)).testBit (q / d))
  | 0, q, _ => by simp
  | m + 1, q, hm => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      testBit_innerT d m (rowF d X m) (by omega) d, testBit_transF_aux d X m q (by omega)]
    by_cases h1 : q % d = m
    · rw [h1]
      simp
    · have : (q % d < m + 1) ↔ (q % d < m) := by omega
      simp [h1, this]

private theorem testBit_transF (d X q : Nat) : (transF d X).testBit q =
    (decide (q % d < d) && decide (q / d < d) && (rowF d X (q % d)).testBit (q / d)) := by
  unfold transF
  exact testBit_transF_aux d X d q le_rfl

private theorem transposeRows_unpackR_transF (d X : Nat) :
    transposeRows d (unpackR d X) = unpackR d (transF d X) := by
  rw [transposeRows]
  conv_rhs => rw [unpackR]
  congr 1
  funext j
  rw [ofBits]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [CFSG.KC.F2W.testBit_ofBitsFold, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hk : k < d
  · have hget : (unpackR d X)[k]?.getD 0 = rowF d X k := by
      simp [unpackR, hk, CFSG.KC.F2W.rowF_eq]
    rw [hget, testBit_transF]
    have h1 : (k + d * j.val) % d = k := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    have h2 : (k + d * j.val) / d = j.val := by
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hk, Nat.zero_add]
    simp [hk, h1, h2, j.isLt]
  · simp [hk]

private theorem colCF_hf (d X j : Nat) :
    ∀ i < d, (fun i => nIf(bit X (d * i + j), nat_lit 1, nat_lit 0)) i < 2 ^ 1 := by
  intro i _
  dsimp only
  cases bit X (d * i + j) <;> decide

private theorem testBit_colCF (d X j r : Nat) :
    (colCF d X j).testBit r = (decide (r < d) && X.testBit (d * r + j)) := by
  have key := CFSG.KC.F2W.testBit_orN_fields (colCF_hf d X j) r
  beta_reduce at key
  unfold colCF
  rw [key, Nat.one_mul, Nat.div_one, Nat.mod_one, CFSG.KC.F2W.bit_eq]
  cases X.testBit (d * r + j) <;> simp

private theorem colCF_lt (d X j : Nat) : colCF d X j < 2 ^ d := by
  have h := CFSG.KC.F2W.orN_fields_lt (colCF_hf d X j)
  beta_reduce at h
  exact lt_of_lt_of_eq h (by rw [Nat.one_mul])

theorem transCF_eq (d X : Nat) : transCF d X = transF d X := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [transCF, CFSG.KC.F2W.testBit_orN_fields (fun j _ => colCF_lt d X j), testBit_colCF,
    testBit_transF]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h1 : q % d < d := Nat.mod_lt q hd
    by_cases hq : q < d * d
    · have h2 : q / d < d := Nat.div_lt_of_lt_mul hq
      rw [CFSG.KC.F2W.testBit_rowF d X _ _ h2, Nat.mul_comm d (q % d)]
      simp [hq, h1, h2]
    · have h2 : ¬ q / d < d := by
        rw [Nat.not_lt, Nat.le_div_iff_mul_le hd]
        omega
      simp [hq, h2]

private theorem lowBitRK_eq (d v : Nat) : ∀ m, m ≤ d →
    lowBitRK d v m = ((List.range m).find? fun j => v.testBit j).getD d
  | 0, _ => rfl
  | m + 1, hm => by
    have ih := lowBitRK_eq d v m (by omega)
    change nIf(Nat.blt (lowBitRK d v m) d, lowBitRK d v m, nIf(bit v m, m, d)) = _
    rw [List.range_succ, List.find?_append, ih, CFSG.KC.F2W.bit_eq]
    cases h : (List.range m).find? fun j => v.testBit j with
    | none =>
      have hb : Nat.blt d d = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
        omega
      simp only [Option.getD_none, Option.none_or, hb]
      cases hv : v.testBit m <;> simp [hv]
    | some j =>
      have hj : j < m := List.mem_range.1 (List.mem_of_find?_eq_some h)
      have hb : Nat.blt j d = true := by
        rw [Nat.blt_eq]
        omega
      simp only [Option.getD_some, Option.some_or, hb]

private theorem redRK_eq (L : List (Nat × Nat × Nat)) : ∀ ic : Nat × Nat, redRK L ic =
    L.foldl (fun (acc : Nat × Nat) (e : Nat × Nat × Nat) =>
      if acc.1.testBit e.1 then (acc.1 ^^^ e.2.1, acc.2 ^^^ e.2.2) else acc) ic := by
  induction L with
  | nil => intro ic; rfl
  | cons e L ih =>
    intro ic
    rw [List.foldl_cons, ← ih]
    change redRK L (Bool.rec (motive := fun _ => Nat × Nat) ic
      (Nat.xor ic.1 e.2.1, Nat.xor ic.2 e.2.2) (bit ic.1 e.1)) = _
    rw [CFSG.KC.F2W.bit_eq]
    cases ic.1.testBit e.1 <;> rfl

private theorem clrRK_eq (p v c : Nat) (L : List (Nat × Nat × Nat)) : clrRK p v c L =
    L.map (fun e => if e.2.1.testBit p then (e.1, e.2.1 ^^^ v, e.2.2 ^^^ c) else e) ++
      [(p, v, c)] := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    change Bool.rec (motive := fun _ => List (Nat × Nat × Nat)) (e :: clrRK p v c L)
      ((e.1, Nat.xor e.2.1 v, Nat.xor e.2.2 c) :: clrRK p v c L) (bit e.2.1 p) = _
    rw [ih, CFSG.KC.F2W.bit_eq, List.map_cons, List.cons_append]
    cases e.2.1.testBit p <;> rfl

private theorem stepRK_eq (d : Nat) (acc : List (Nat × Nat × Nat) × List Nat) (ic : Nat × Nat) :
    stepRK d acc ic = match insertRref d acc.1 ic with
      | (L, none) => (L, acc.2)
      | (L, some c) => (L, c :: acc.2) := by
  unfold stepRK insertRref
  dsimp only
  rw [← redRK_eq]
  cases hb : Nat.beq (redRK acc.1 ic).1 0
  · have h := Nat.ne_of_beq_eq_false hb
    have h' : ¬ (((redRK acc.1 ic).1 == 0) = true) := by simpa using h
    rw [if_neg h', clrRK_eq, lowBitRK_eq d _ d le_rfl]
    rfl
  · have h := Nat.eq_of_beq_eq_true hb
    have h' : ((redRK acc.1 ic).1 == 0) = true := by simpa using h
    rw [if_pos h']

theorem rrefImK_eq (d : Nat) (img : Nat → Nat) : rrefImK d img = rrefImages d img := by
  have key : ∀ n, (Nat.rec (motive := fun _ => List (Nat × Nat × Nat) × List Nat) ([], [])
      (fun i acc => stepRK d acc (img i, 1 <<< i)) n) =
      (List.range n).foldl (fun (acc : List (Nat × Nat × Nat) × List Nat) i =>
        match insertRref d acc.1 (img i, 1 <<< i) with
        | (L, none) => (L, acc.2)
        | (L, some c) => (L, c :: acc.2)) ([], []) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih]
      exact stepRK_eq d _ _
  exact key d

private theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

private theorem testBit_pw (p q : Nat) : (1 <<< p).testBit q = decide (p = q) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

private theorem land_pw (w p : Nat) : w &&& 1 <<< p = if w.testBit p then 1 <<< p else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, testBit_pw]
  by_cases hb : w.testBit p = true
  · rw [if_pos hb, testBit_pw]
    by_cases hi : p = i
    · subst hi
      simp [hb]
    · simp [hi]
  · rw [if_neg hb, Nat.zero_testBit]
    by_cases hi : p = i
    · subst hi
      simp [hb]
    · simp [hi]

private theorem pos_land_pw (w p : Nat) : 0 < w &&& 1 <<< p ↔ w.testBit p = true := by
  rw [land_pw]
  by_cases hb : w.testBit p = true
  · rw [if_pos hb, Nat.one_shiftLeft]
    exact ⟨fun _ => hb, fun _ => Nat.two_pow_pos p⟩
  · rw [if_neg hb]
    exact ⟨fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h hb⟩

private theorem land_pw_eq_zero (w p : Nat) : w &&& 1 <<< p = 0 ↔ w.testBit p = false := by
  rw [land_pw]
  by_cases hb : w.testBit p = true
  · rw [if_pos hb, Nat.one_shiftLeft, hb]
    simp
  · rw [if_neg hb]
    simpa using hb

private theorem pivOKR_iff (d : Nat) : ∀ (A : List (Nat × Nat)) (acc : Nat),
    pivOKR d A acc = true ↔ (∀ e ∈ A, e.1 < d ∧ e.2.testBit e.1 = true) ∧
      (A.map Prod.fst).Nodup ∧ ∀ e ∈ A, acc.testBit e.1 = false := by
  intro A
  induction A with
  | nil =>
    intro acc
    change true = true ↔ _
    simp
  | cons e A ih =>
    intro acc
    change CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.blt e.1 d) (Nat.blt 0 (e.2 &&& 1 <<< e.1)))
      (CFSG.KLie.CT.andB (Nat.beq (acc &&& 1 <<< e.1) 0)
        (pivOKR d A (acc ||| 1 <<< e.1))) = true ↔ _
    rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Nat.blt_eq, Nat.blt_eq, Nat.beq_eq, pos_land_pw, land_pw_eq_zero, ih]
    simp only [Nat.testBit_lor, testBit_pw, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      List.map_cons, List.nodup_cons, List.mem_map, List.mem_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩
      refine ⟨fun x hx => ?_, ⟨?_, h5⟩, fun x hx => ?_⟩
      · rcases hx with rfl | hx
        · exact ⟨h1, h2⟩
        · exact h4 x hx
      · rintro ⟨a, ha, hae⟩
        exact (h6 a ha).2 hae.symm
      · rcases hx with rfl | hx
        · exact h3
        · exact (h6 x hx).1
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
      refine ⟨h1 e (Or.inl rfl), h4 e (Or.inl rfl), fun x hx => h1 x (Or.inr hx), h3,
        fun x hx => ⟨h4 x (Or.inr hx), fun hex => h2 ⟨x, hx, hex.symm⟩⟩⟩

private theorem pivMaskR_testBit (A : List (Nat × Nat)) (q : Nat) :
    (pivMaskR A).testBit q = true ↔ ∃ e ∈ A, e.1 = q := by
  induction A with
  | nil =>
    change (0 : Nat).testBit q = true ↔ _
    simp
  | cons e A ih =>
    change (1 <<< e.1 ||| pivMaskR A).testBit q = true ↔ _
    rw [Nat.testBit_lor, Bool.or_eq_true, testBit_pw, decide_eq_true_eq, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

private theorem clrOKR_iff (P : Nat) (A : List (Nat × Nat)) :
    clrOKR P A = true ↔ ∀ e ∈ A, e.2 &&& P = 1 <<< e.1 := by
  induction A with
  | nil =>
    change true = true ↔ _
    simp
  | cons e A ih =>
    change CFSG.KLie.CT.andB (Nat.beq (e.2 &&& P) (1 <<< e.1)) (clrOKR P A) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, Nat.beq_eq, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

private theorem rrefOKL_iff (d : Nat) (A : List (Nat × Nat)) :
    rrefOKL d A = true ↔ (∀ e ∈ A, e.1 < d ∧ e.2.testBit e.1 = true) ∧
      ∀ (i j : Nat) (hi : i < A.length) (hj : j < A.length), i ≠ j →
        (A[j].2.testBit A[i].1) = false := by
  unfold rrefOKL
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · intro h i j hi hj hij
    have := h (A[i], i) (List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi))
      (A[j], j) (List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hj))
    simpa [hij] using this
  · rintro h ⟨a, i⟩ hi ⟨b, j⟩ hj
    rw [List.mem_zipIdx_iff_getElem?] at hi hj
    dsimp only at hi hj ⊢
    obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hi
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, h i j hi' hj' hij]

theorem rrefOKK_eq (d : Nat) (A : List (Nat × Nat)) : rrefOKK d A = rrefOKL d A := by
  rw [Bool.eq_iff_iff]
  change CFSG.KLie.CT.andB (pivOKR d A 0) (clrOKR (pivMaskR A) A) = true ↔ _
  rw [andB_eq, Bool.and_eq_true, pivOKR_iff, clrOKR_iff, rrefOKL_iff]
  simp only [Nat.zero_testBit, eq_self_iff_true, implies_true, and_true]
  have hne : ∀ (hnd : (A.map Prod.fst).Nodup) (i j : Nat) (hi : i < A.length)
      (hj : j < A.length), i ≠ j → A[i].1 ≠ A[j].1 := by
    intro hnd i j hi hj hij h
    apply hij
    have hi' : i < (A.map Prod.fst).length := by simpa using hi
    have hj' : j < (A.map Prod.fst).length := by simpa using hj
    exact (hnd.getElem_inj_iff (hi := hi') (hj := hj')).1 (by simpa using h)
  constructor
  · rintro ⟨⟨h1, hnd⟩, hclr⟩
    refine ⟨h1, fun i j hi hj hij => ?_⟩
    have hc := congrArg (fun n => n.testBit A[i].1) (hclr A[j] (List.getElem_mem hj))
    simp only [Nat.testBit_land, testBit_pw] at hc
    have hP : (pivMaskR A).testBit A[i].1 = true :=
      (pivMaskR_testBit A _).2 ⟨A[i], List.getElem_mem hi, rfl⟩
    rw [hP, Bool.and_true] at hc
    rw [hc]
    exact decide_eq_false (hne hnd i j hi hj hij).symm
  · rintro ⟨h1, hpair⟩
    have hnd : (A.map Prod.fst).Nodup := by
      rw [List.Nodup, List.pairwise_iff_getElem]
      intro i j hi hj hij heq
      have hi' : i < A.length := by simpa using hi
      have hj' : j < A.length := by simpa using hj
      have h := hpair i j hi' hj' (Nat.ne_of_lt hij)
      simp only [List.getElem_map] at heq
      rw [heq, (h1 _ (List.getElem_mem hj')).2] at h
      exact absurd h (by decide)
    refine ⟨⟨h1, hnd⟩, fun f hf => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_land, testBit_pw]
    by_cases hq : (pivMaskR A).testBit q = true
    · obtain ⟨e, he, rfl⟩ := (pivMaskR_testBit A q).1 hq
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      rw [hq, Bool.and_true]
      by_cases hij : i = j
      · subst hij
        rw [(h1 _ he).2]
        simp
      · rw [hpair i j hi hj hij]
        exact (decide_eq_false (hne hnd i j hi hj hij).symm).symm
    · rw [Bool.not_eq_true] at hq
      rw [hq, Bool.and_false]
      refine (decide_eq_false fun h => ?_).symm
      have := (pivMaskR_testBit A q).2 ⟨A[j], List.getElem_mem hj, h⟩
      rw [hq] at this
      exact absurd this (by decide)

theorem fixDimFK_eq (d X k : Nat) : fixDimFK d X k = fixDimK d X k := by
  simp only [fixDimFK, fixDimK, fixCertFK, fixCertK, transCF_eq, rrefImK_eq, rrefOKK_eq]

theorem fixRepsFK_eq (d X Y Z : Nat) : fixRepsFK d X Y Z = fixRepsK d X Y Z := by
  simp only [fixRepsFK, fixRepsK, fixDimFK_eq]

private theorem toArray_getElem! {A : List (Nat × Nat)} {i : Nat} (hi : i < A.length) :
    A.toArray[i]! = A[i] := by
  rw [getElem!_pos A.toArray i (by simpa using hi)]
  simp

private theorem rrefOK_toArray (d : Nat) (A : List (Nat × Nat)) :
    rrefOK d A.toArray = rrefOKL d A := by
  unfold rrefOK rrefOKL
  rw [List.all_toArray, List.size_toArray]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · rintro h ⟨a, i⟩ hi ⟨b, j⟩ hj
    rw [List.mem_zipIdx_iff_getElem?] at hi hj
    dsimp only at hi hj ⊢
    obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hi
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
    have := h i hi' j hj'
    rwa [toArray_getElem! hi', toArray_getElem! hj'] at this
  · intro h i hi j hj
    have := h (A[i], i) (List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi))
      (A[j], j) (List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hj))
    rwa [toArray_getElem! hi, toArray_getElem! hj]

private theorem colFixT_unpackR (d T v : Nat) : colFixT d (unpackR d T) v = colFixK d T v := by
  rw [colFixT, colFixK, CFSG.KC.F2W.vecMulN_unpackR]

private theorem fixCertOK_toArray (d T : Nat) (K : List (Nat × Nat))
    (I : List (Nat × Nat × Nat)) (k : Nat) :
    fixCertOK d (unpackR d T) K.toArray I.toArray k = fixCertK d T K I k := by
  unfold fixCertOK fixCertK
  rw [List.all_toArray]
  simp only [colFixT_unpackR, List.size_toArray, List.map_toArray, rrefOK_toArray]

theorem fixDimOK_of_K {d X k : Nat} (h : fixDimK d X k = true) :
    fixDimOK d (unpackR d X) k = true := by
  unfold fixDimOK
  dsimp only
  rw [transposeRows_unpackR_transF]
  simp only [colFixT_unpackR]
  rw [show ∀ vs, rref d vs = (rrefL d vs).toArray from fun _ => rfl, fixCertOK_toArray]
  exact h

theorem powRows_unpackR (d M : Nat) : ∀ e : Nat,
    powRows d (unpackR d M) e = unpackR d (powLK d M e)
  | 0 => (CFSG.KC.OpsK.unpackR_idF d).symm
  | e + 1 => by
    change mulRows d (powRows d (unpackR d M) e) (unpackR d M) = unpackR d (mulF d (powLK d M e) M)
    rw [powRows_unpackR d M e, CFSG.KC.F2W.mulRows_unpackR]

theorem mulRows_eq (d A B : Nat) : mulRows d (unpackR d A) (unpackR d B) = unpackR d (mulF d A B) :=
  CFSG.KC.F2W.mulRows_unpackR d A B

variable {A B : Nat} {csA csB : List Char}

theorem regs_eq (hA : m1Bind csA 112 A = true) (hB : m1Bind csB 112 B = true)
    (hsA : j4Sylow11Data.seedA = String.ofList csA) (hsB : j4Sylow11Data.seedB = String.ofList csB)
    {r : Nat} (hr : r < 31) :
    j4R[r]! = unpackR 112 (CFSG.KC.OpsF2K.getR 112 (regsK A B) r) :=
  CFSG.KC.OpsF2K.regs_get hA hB hsA hsB (by decide) (by decide) hr

theorem z_eq (hA : m1Bind csA 112 A = true) (hB : m1Bind csB 112 B = true)
    (hsA : j4Sylow11Data.seedA = String.ofList csA) (hsB : j4Sylow11Data.seedB = String.ofList csB) :
    j4Z = unpackR 112 (zK A B) := by
  unfold j4Z j4X j4Y zK xK yK
  rw [regs_eq hA hB hsA hsB (by decide), regs_eq hA hB hsA hsB (by decide),
    CFSG.KC.OpsF2K.unpackR_commMK (by decide)]

theorem check_of_K (hA : m1Bind csA 112 A = true) (hB : m1Bind csB 112 B = true)
    (hsA : j4Sylow11Data.seedA = String.ofList csA) (hsB : j4Sylow11Data.seedB = String.ofList csB)
    (h40 : Nat.beq (CFSG.KC.OpsF2K.powK 112 (hK A B) 40) (idF 112) = true)
    (hcx : CFSG.KC.OpsF2K.conjK 112 (hK A B) (xK A B) (mulF 112 (mulF 112 (powLK 112 (xK A B) 0)
      (powLK 112 (yK A B) 7)) (powLK 112 (zK A B) 1)) = true)
    (hcy : CFSG.KC.OpsF2K.conjK 112 (hK A B) (yK A B) (mulF 112 (mulF 112 (powLK 112 (xK A B) 6)
      (powLK 112 (yK A B) 9)) (powLK 112 (zK A B) 6)) = true)
    (hcz : CFSG.KC.OpsF2K.conjK 112 (hK A B) (zK A B) (powLK 112 (zK A B) 2) = true)
    (hreps : fixRepsK 112 (xK A B) (yK A B) (zK A B) = true)
    (hc : fixDimFK 112 (zK A B) 2 = true) :
    ((ops2 112).eq ((ops2 112).pow j4H 40) (ops2 112).one = true)
    ∧ ((ops2 112).conjOK j4H j4X (j4Word 0 7 1) = true)
    ∧ ((ops2 112).conjOK j4H j4Y (j4Word 6 9 6) = true)
    ∧ ((ops2 112).conjOK j4H j4Z (powRows 112 j4Z 2) = true)
    ∧ (j4FixRepsOK = true)
    ∧ (fixDimOK 112 j4Z 2 = true) := by
  have hX : j4X = unpackR 112 (xK A B) := regs_eq hA hB hsA hsB (by decide)
  have hY : j4Y = unpackR 112 (yK A B) := regs_eq hA hB hsA hsB (by decide)
  have hH : j4H = unpackR 112 (hK A B) := regs_eq hA hB hsA hsB (by decide)
  have hZ : j4Z = unpackR 112 (zK A B) := z_eq hA hB hsA hsB
  have hW : ∀ a b c, j4Word a b c = unpackR 112 (mulF 112 (mulF 112 (powLK 112 (xK A B) a)
      (powLK 112 (yK A B) b)) (powLK 112 (zK A B) c)) := by
    intro a b c
    unfold j4Word
    rw [hX, hY, hZ, powRows_unpackR, powRows_unpackR, powRows_unpackR, mulRows_eq, mulRows_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hH, ← CFSG.KC.OpsF2K.unpackR_powK (by decide), ← CFSG.KC.OpsF2K.unpackR_idF_eq_one]
    exact CFSG.KC.OpsF2K.eq_of_beq h40
  · rw [hH, hX, hW]
    exact CFSG.KC.OpsF2K.conjOK_of_conjK hcx
  · rw [hH, hY, hW]
    exact CFSG.KC.OpsF2K.conjOK_of_conjK hcy
  · rw [hH, hZ, powRows_unpackR]
    exact CFSG.KC.OpsF2K.conjOK_of_conjK hcz
  · unfold j4FixRepsOK
    unfold fixRepsK at hreps
    rw [Bool.and_eq_true] at hreps ⊢
    refine ⟨?_, List.all_eq_true.2 fun b hb => ?_⟩
    · rw [hW]
      exact fixDimOK_of_K hreps.1
    · rw [hW]
      exact fixDimOK_of_K (List.all_eq_true.1 hreps.2 b hb)
  · rw [hZ]
    exact fixDimOK_of_K ((fixDimFK_eq 112 _ 2).symm.trans hc)

end CFSG.KC.J4Fix

end
