module

public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.StripLib
public import CFSG.Certificates.Kernel.BSeed.Sound

public section

namespace CFSG.KC.BM.Fix

open CFSG.KC.BM CFSG.KC.BSeed CFSG.KC.YModel CFSG.KC.BM.Lat CFSG.KC.BM.SL
open scoped Matrix

@[expose] noncomputable def stripMatn (S : List Nat) : Matrix (Fin 4371) (Fin 4371) (ZMod 2) :=
  fun i j => if (lget S (i.val / 64)).testBit (64 * j.val + i.val % 64) then 1 else 0

inductive AllStripsN (Ws : List (List Nat)) : List Nat → List Nat → Prop
  | nil : AllStripsN Ws [] []
  | cons (a c : Nat) (as cs : List Nat) :
      Nat.beq (mulWn (nat_lit 4371) Ws a) c = true → AllStripsN Ws as cs →
        AllStripsN Ws (a :: as) (c :: cs)

inductive AllBlocksN : List (List Nat) → List Nat → Nat → Prop
  | nil (s : Nat) : AllBlocksN [] [] s
  | cons (blk : List Nat) (T s : Nat) (R : List (List Nat)) (S : List Nat) :
      blockOKn (nat_lit 4371) blk T s = true → AllBlocksN R S (Nat.succ s) →
        AllBlocksN (blk :: R) (T :: S) s

inductive AllStripsX (Q : List Nat) : List Nat → List Nat → Prop
  | nil : AllStripsX Q [] []
  | cons (a c : Nat) (as cs : List Nat) :
      Nat.beq (Nat.xor (mulS Q a) a) c = true → AllStripsX Q as cs →
        AllStripsX Q (a :: as) (c :: cs)

@[expose] noncomputable def idStripsN : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun k ih acc => ih (List.cons (idSn (nat_lit 4371) k) acc)) (nat_lit 69) List.nil

@[expose] def vecOf (x : Nat) : Fin 4371 → ZMod 2 := fun j => if x.testBit j then 1 else 0

@[expose] noncomputable def qE (Q : List (List Nat)) (s : Nat) : List Nat :=
  if s < 18 then lgetL Q s
  else if s = 18 then dropLastL (lgetL Q 18)
  else if s < 68 then consN (lastL (lgetL Q (s - 1))) (dropLastL (lgetL Q s))
  else consN (lastL (lgetL Q 67)) (lgetL Q 68)

@[expose] noncomputable def quotOK (f : Nat) (C Q : List (List Nat)) (s : Nat) : Bool :=
  andB (andB (Nat.beq (lenL (lgetL C s)) (rowsSn 4371 s)) (Nat.beq (lenL (lgetL Q s)) (rowsS s)))
    (quotBlk 1197 f s (lgetL C s) (qE Q s))

theorem stripMatn_eq (S : List Nat) : stripMatn S = stripMatG 4371 S := rfl

theorem recOf_eq (R : List (List Nat)) (i : Nat) : recOf R i = (R.getD (i / 64) []).getD (i % 64) 0 := by
  unfold recOf
  rw [lget_eq, lgetL_eq]
  rfl

theorem allStripsN_spec {Ws : List (List Nat)} : ∀ {A C : List Nat}, AllStripsN Ws A C →
    C = A.map (mulWn 4371 Ws)
  | _, _, .nil => rfl
  | _, _, .cons a c as cs hb h => by
    rw [allStripsN_spec h, List.map_cons, ← Nat.eq_of_beq_eq_true hb]

theorem allBlocksN_spec : ∀ {R : List (List Nat)} {S : List Nat} {s0 : Nat}, AllBlocksN R S s0 →
    R.length = S.length ∧ ∀ i < R.length, blockOKn 4371 (R.getD i []) (S.getD i 0) (s0 + i) = true
  | _, _, _, .nil _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | _, _, _, .cons blk T s R S hb h => by
    obtain ⟨h1, h2⟩ := allBlocksN_spec h
    refine ⟨by simp [h1], ?_⟩
    intro i hi
    cases i with
    | zero => simpa using hb
    | succ i =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      have := h2 i (by simp at hi; omega)
      rwa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 i] at this

theorem allStripsX_spec {Q : List Nat} : ∀ {P R : List Nat}, AllStripsX Q P R →
    R = P.map (fun a => mulSn 4370 Q a ^^^ a)
  | _, _, .nil => rfl
  | _, _, .cons a c as cs hb h => by
    rw [allStripsX_spec h, List.map_cons, ← Nat.eq_of_beq_eq_true hb]
    rfl

theorem ech_linIndep {n : Nat} {M : List Nat} (hM : M.length = 69) (act : Nat → Bool)
    (pass : Nat → Nat → Bool) (st0 : Nat)
    (h : (List.range (64 * M.length)).foldl (fun st i => if act i then echStep (rowAt (SMn n) M i) st
      else if pass i (rowAt (SMn n) M i) then st else 0) st0 ≠ 0)
    (hn : n ≤ 4416) (P : Fin n → Prop) (hP : ∀ i, P i → act i.val = true) :
    LinearIndependent (ZMod 2) (fun i : {i : Fin n // P i} => stripMatG n M i.val) := by
  obtain ⟨A, _, C, _⟩ := ech_fold act pass (rowAt (SMn n) M) st0 _ h
  apply stripMatG_linIndep (fun i : {i : Fin n // P i} => i.val)
  · intro i
    exact A _ (by have := i.val.isLt; omega) (hP _ i.property)
  · intro i i' e
    by_contra hne
    have hne' : i.val.val ≠ i'.val.val := fun e' => hne (Subtype.ext (Fin.ext e'))
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
    · have := C _ _ hlt (by have := i'.val.isLt; omega) (hP _ i.property) (hP _ i'.property)
      omega
    · have := C _ _ hlt (by have := i.val.isLt; omega) (hP _ i'.property) (hP _ i.property)
      omega

theorem stripMatG_row_zero {n : Nat} {M : List Nat} {i : Fin n} (h : rowAt (SMn n) M i.val = 0) :
    stripMatG n M i = 0 := by
  funext j
  rw [stripMatG_apply, Pi.zero_apply]
  have e := testBit_rowAt n M i.val j.val
  rw [h, Nat.zero_testBit, decide_eq_true j.isLt, Bool.and_true] at e
  rw [← e, bz_false]

theorem notB_beq {x : Nat} (h : notB (Nat.beq x 0) = true) : x ≠ 0 := by
  intro e
  rw [e] at h
  exact absurd h (by decide)

set_option exponentiation.threshold 300000 in
theorem topRow_ne : topRow ≠ 0 := by
  unfold topRow
  rw [nshl, Nat.one_shiftLeft]
  exact (Nat.two_pow_pos _).ne'

theorem projRows_eq (p f : Nat) : ∀ (R : List Nat) (i0 : Nat),
    projRows p f R i0 = (if i0 ≤ p then R.eraseIdx (p - i0) else R).map (projRow p f)
  | [], i0 => by simp [projRows]
  | r :: R, i0 => by
    change Bool.rec (motive := fun _ => List Nat) (List.cons (projRow p f r) (projRows p f R (Nat.succ i0)))
      (projRows p f R (Nat.succ i0)) (Nat.beq i0 p) = _
    rw [projRows_eq p f R]
    by_cases h : i0 = p
    · subst h
      rw [Nat.beq_refl]
      simp
    · have hb : Nat.beq i0 p = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
        exact h
      rw [hb]
      by_cases h2 : i0 < p
      · have e : p - i0 = (p - Nat.succ i0) + 1 := by omega
        rw [ite_eq_left (by omega : Nat.succ i0 ≤ p), ite_eq_left (by omega : i0 ≤ p), e,
          List.eraseIdx_cons_succ, List.map_cons]
      · rw [ite_eq_right (by omega : ¬ Nat.succ i0 ≤ p), ite_eq_right (by omega : ¬ i0 ≤ p), List.map_cons]

theorem getD_eraseIdx : ∀ (L : List Nat) (p i : Nat),
    (L.eraseIdx p).getD i 0 = if i < p then L.getD i 0 else L.getD (i + 1) 0
  | [], p, i => by simp
  | x :: L, 0, i => by simp
  | x :: L, p + 1, 0 => by simp
  | x :: L, p + 1, i + 1 => by
    rw [List.eraseIdx_cons_succ, List.getD_cons_succ, getD_eraseIdx L p i, List.getD_cons_succ,
      List.getD_cons_succ]
    by_cases h : i < p
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem lastL_aux : ∀ (L : List Nat) (d : Nat),
    (List.rec (motive := fun _ => Nat → Nat) (fun d => d) (fun x _ ih _ => ih x) L d : Nat) =
      (d :: L).getD L.length 0
  | [], d => rfl
  | x :: L, d => by
    change (List.rec (motive := fun _ => Nat → Nat) (fun d => d) (fun x _ ih _ => ih x) L x : Nat) = _
    rw [lastL_aux L x, List.length_cons, List.getD_cons_succ]

theorem lastL_eq (L : List Nat) : lastL L = (0 :: L).getD L.length 0 := lastL_aux L 0

theorem dropLastL_eq : ∀ (L : List Nat), dropLastL L = L.dropLast
  | [] => rfl
  | [x] => rfl
  | x :: y :: L => by
    change x :: dropLastL (y :: L) = _
    rw [dropLastL_eq (y :: L), List.dropLast_cons_cons]

theorem getD_dropLast {L : List Nat} {i : Nat} (h : i + 1 < L.length) :
    L.dropLast.getD i 0 = L.getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega),
    List.getElem_dropLast]

theorem stripMatn_mul_of_allStrips {Ws : List (List Nat)} {A C : List Nat}
    (hW : ∀ W ∈ Ws, wfMatn 4371 W = true) (hA : wfMatn 4371 A = true) (h : AllStripsN Ws A C) :
    (Ws.map stripMatn).foldl (· * ·) (stripMatn A) = stripMatn C := by
  rw [allStripsN_spec h]
  exact stripMatG_foldl (by norm_num) hW (wf_bit hA).1

theorem stripMatn_mul_eq_one {Ws : List (List Nat)} {A : List Nat}
    (hW : ∀ W ∈ Ws, wfMatn 4371 W = true) (hA : wfMatn 4371 A = true)
    (h : AllStripsN Ws A idStripsN) :
    (Ws.map stripMatn).foldl (· * ·) (stripMatn A) = 1 := by
  rw [stripMatn_mul_of_allStrips hW hA h, stripMatn_eq]
  exact stripMatG_id (by norm_num) (idStripsG_eq 4371)

theorem rowsMat_eq_stripMatn {R : List (List Nat)} {S : List Nat} (h : AllBlocksN R S 0)
    (hS : wfMatn 4371 S = true) : rowsMat 4371 (recOf R) = stripMatn S := by
  obtain ⟨hl, hb⟩ := allBlocksN_spec h
  have hS69 := (wf_bit hS).1
  have hR : ∀ s < 69, (R.getD s []).length = rowsSn 4371 s ∧
      sob 282624 4371 (R.getD s []) 0 0 = S.getD s 0 := fun s hs => by
    have h' := hb s (by omega)
    unfold blockOKn at h'
    rw [andB_eq, Bool.and_eq_true, Nat.zero_add] at h'
    exact ⟨by rw [← lenL_eq]; exact Nat.eq_of_beq_eq_true h'.1, Nat.eq_of_beq_eq_true h'.2⟩
  ext i j
  have := (rows_of_blocks (by norm_num) (by norm_num) hS hR i.isLt).2 j.val
  change bz ((recOf R i.val).testBit j.val) = stripMatG 4371 S i j
  rw [stripMatG_apply, recOf_eq, this]

theorem xorStrips_sound {A B C D : List Nat}
    (h : ∀ s < 69, Nat.beq (Nat.xor (lget A s) (Nat.xor (lget B s) (lget C s))) (lget D s) = true) :
    stripMatn D = stripMatn A + stripMatn B + stripMatn C := by
  ext i j
  simp only [Matrix.add_apply, stripMatn_eq, stripMatG_apply]
  have e := Nat.eq_of_beq_eq_true (h (i.val / 64) (by omega))
  rw [lget_eq, lget_eq, lget_eq, lget_eq, nxor, nxor] at e
  rw [← e, Nat.testBit_xor, Nat.testBit_xor, bz_xor, bz_xor, add_assoc]

theorem stripMat_mul_add_one {Q P R : List Nat} (hQ : wfMat Q = true) (hP : wfMat P = true)
    (h : AllStripsX Q P R) : stripMat P * (stripMat Q + 1) = stripMat R := by
  rw [wfMat_eq] at hQ hP
  have hl := (wf_bit hP).1
  rw [mul_add, mul_one, stripMat_eq, stripMat_eq, stripMat_eq, stripMatG_mul (by norm_num) hl hQ,
    allStripsX_spec h]
  ext i j
  have hi : i.val / 64 < P.length := by omega
  rw [Matrix.add_apply, stripMatG_apply, stripMatG_apply, stripMatG_apply, getD_map_of_lt hi,
    getD_map_of_lt hi, Nat.testBit_xor, bz_xor]

theorem vecMul_sound {Rb : List (List Nat)} (hn : lenLL Rb = 69)
    (hl : ∀ s < 69, lenL (lgetL Rb s) = rowsSn 4371 s) (v : Nat) :
    vecOf (vecMul Rb v) = vecOf v ᵥ* rowsMat 4371 (recOf Rb) := by
  rw [lenLL_eq] at hn
  have hl' : ∀ s < 69, (Rb.getD s []).length = rowsSn 4371 s := fun s hs => by
    rw [← lgetL_eq, ← lenL_eq]
    exact hl s hs
  have hfl := flatten_getD Rb (fun s hs => by rw [hl' s (by omega), rowsSn_eq]; omega)
    (fun s hs => by rw [hl' s (by omega), rowsSn_eq]; omega)
  funext j
  change bz ((vecMul Rb v).testBit j.val) = ∑ i : Fin 4371, bz (v.testBit i.val) *
    bz ((recOf Rb i.val).testBit j.val)
  rw [vecMul_eq_vOuter, vOuter_eq, VL_bit, Nat.zero_testBit, bz_false, zero_add,
    Fin.sum_univ_eq_sum_range (fun i => bz (v.testBit i) * bz ((recOf Rb i).testBit j.val)) 4371]
  have hz : ∀ m, 4371 ≤ m → recOf Rb m = 0 := by
    intro m hm
    rw [recOf_eq]
    by_cases hs : m / 64 < 69
    · apply List.getD_eq_default
      rw [hl' _ hs, rowsSn_eq]
      omega
    · rw [List.getD_eq_default Rb [] (by omega : Rb.length ≤ m / 64)]
      simp
  have e1 : ∑ m ∈ Finset.range Rb.flatten.length, bz (v.testBit m) *
      bz ((Rb.flatten.getD m 0).testBit j.val) = ∑ m ∈ Finset.range (Rb.flatten.length + 4371),
        bz (v.testBit m) * bz ((Rb.flatten.getD m 0).testBit j.val) := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    rw [Finset.mem_range, Nat.not_lt] at hm
    rw [List.getD_eq_default _ _ hm, Nat.zero_testBit, bz_false, mul_zero]
  have e2 : ∑ m ∈ Finset.range 4371, bz (v.testBit m) * bz ((recOf Rb m).testBit j.val) =
      ∑ m ∈ Finset.range (Rb.flatten.length + 4371),
        bz (v.testBit m) * bz ((recOf Rb m).testBit j.val) := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    rw [Finset.mem_range, Nat.not_lt] at hm
    rw [hz m hm, Nat.zero_testBit, bz_false, mul_zero]
  rw [e1, e2]
  apply Finset.sum_congr rfl
  intro m _
  rw [hfl, recOf_eq]

theorem quotOK_sound {f : Nat} {C Q : List (List Nat)}
    (_hn : andB (Nat.beq (lenLL C) 69) (Nat.beq (lenLL Q) 69) = true)
    (h : ∀ s < 69, quotOK f C Q s = true) :
    ∀ k < 4370, recOf Q k = projRow 1197 f (recOf C (if k < 1197 then k else k + 1)) := by
  intro k hk
  have hb : ∀ s < 69, (C.getD s []).length = rowsSn 4371 s ∧
      (Q.getD s []).length = rowsSn 4370 s ∧
      qE Q s = (if 64 * s ≤ 1197 then (C.getD s []).eraseIdx (1197 - 64 * s) else C.getD s []).map
        (projRow 1197 f) := by
    intro s hs
    have h' := h s hs
    unfold quotOK quotBlk at h'
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    refine ⟨?_, ?_, ?_⟩
    · rw [← lgetL_eq, ← lenL_eq]
      exact Nat.eq_of_beq_eq_true h1
    · rw [← lgetL_eq, ← lenL_eq]
      exact Nat.eq_of_beq_eq_true h2
    · rw [← eqL_eq _ _ h3, projRows_eq, lgetL_eq]
      rfl
  have key : ∀ s m, s < 69 → m < (if 64 * s ≤ 1197 then (C.getD s []).eraseIdx (1197 - 64 * s)
      else C.getD s []).length → (qE Q s).getD m 0 = projRow 1197 f
        ((if 64 * s ≤ 1197 then (C.getD s []).eraseIdx (1197 - 64 * s) else C.getD s []).getD m 0) :=
    fun s m hs hm => by rw [(hb s hs).2.2]; exact getD_map_of_lt hm
  rw [recOf_eq, recOf_eq]
  by_cases hk1 : k < 1215
  ·
    have hs : k / 64 < 69 := by omega
    obtain ⟨hCs, hQs, _⟩ := hb _ hs
    rw [rowsSn_eq] at hCs hQs
    have hX : 64 * (k / 64) ≤ 1197 := by omega
    have hlenE := @List.length_eraseIdx _ (C.getD (k / 64) []) (1197 - 64 * (k / 64))
    have e1 := key _ (k % 64) hs (by rw [ite_eq_left hX, hlenE]; split <;> omega)
    rw [ite_eq_left hX, getD_eraseIdx] at e1
    have eL : (qE Q (k / 64)).getD (k % 64) 0 = (Q.getD (k / 64) []).getD (k % 64) 0 := by
      by_cases h18 : k / 64 < 18
      · unfold qE
        rw [ite_eq_left h18, lgetL_eq]
      · have h18' : k / 64 = 18 := by omega
        unfold qE
        rw [ite_eq_right h18, ite_eq_left h18', lgetL_eq, dropLastL_eq, h18']
        rw [h18'] at hQs
        rw [getD_dropLast (by omega)]
    rw [← eL, e1]
    by_cases hm : k % 64 < 1197 - 64 * (k / 64)
    · rw [ite_eq_left hm, ite_eq_left (by omega : k < 1197)]
    · rw [ite_eq_right hm, ite_eq_right (by omega : ¬ k < 1197)]
      have e2 : (k + 1) / 64 = k / 64 := by omega
      have e3 : (k + 1) % 64 = k % 64 + 1 := by omega
      rw [e2, e3]
  ·
    rw [ite_eq_right (by omega : ¬ k < 1197)]
    have hs : (k + 1) / 64 < 69 := by omega
    obtain ⟨hCs, _, _⟩ := hb _ hs
    rw [rowsSn_eq] at hCs
    have hX : ¬ 64 * ((k + 1) / 64) ≤ 1197 := by omega
    have e1 := key _ ((k + 1) % 64) hs (by rw [ite_eq_right hX]; omega)
    rw [ite_eq_right hX] at e1
    rw [← e1]
    have hp : (k + 1) / 64 - 1 < 69 := by omega
    obtain ⟨_, hQp, _⟩ := hb _ hp
    rw [rowsSn_eq] at hQp
    by_cases hm : (k + 1) % 64 = 0
    · have eq1 : k / 64 = (k + 1) / 64 - 1 := by omega
      have eq2 : k % 64 = 63 := by omega
      rw [eq1, eq2, hm]
      have hlast : lastL (lgetL Q ((k + 1) / 64 - 1)) = (Q.getD ((k + 1) / 64 - 1) []).getD 63 0 := by
        rw [lastL_eq, lgetL_eq, hQp]
        have e64 : min 64 (4370 - 64 * ((k + 1) / 64 - 1)) = 63 + 1 := by omega
        rw [e64, List.getD_cons_succ]
      have n18 : ¬ (k + 1) / 64 < 18 := by omega
      have n18' : ¬ (k + 1) / 64 = 18 := by omega
      by_cases h68 : (k + 1) / 64 < 68
      · unfold qE
        rw [ite_eq_right n18, ite_eq_right n18', ite_eq_left h68, consN, List.getD_cons_zero, hlast]
      · unfold qE
        rw [ite_eq_right n18, ite_eq_right n18', ite_eq_right h68, consN, List.getD_cons_zero,
          ← hlast]
        have e67 : (k + 1) / 64 - 1 = 67 := by omega
        rw [e67]
    · have eq1 : k / 64 = (k + 1) / 64 := by omega
      have eq2 : k % 64 = (k + 1) % 64 - 1 := by omega
      obtain ⟨m', hm'⟩ : ∃ m', (k + 1) % 64 = m' + 1 := ⟨(k + 1) % 64 - 1, by omega⟩
      rw [eq1, eq2, hm', Nat.add_sub_cancel]
      obtain ⟨_, hQs, _⟩ := hb _ hs
      rw [rowsSn_eq] at hQs
      have n18 : ¬ (k + 1) / 64 < 18 := by omega
      have n18' : ¬ (k + 1) / 64 = 18 := by omega
      by_cases h68 : (k + 1) / 64 < 68
      · unfold qE
        rw [ite_eq_right n18, ite_eq_right n18', ite_eq_left h68, consN, List.getD_cons_succ,
          lgetL_eq, dropLastL_eq, getD_dropLast (by omega)]
      · unfold qE
        rw [ite_eq_right n18, ite_eq_right n18', ite_eq_right h68, consN, List.getD_cons_succ,
          lgetL_eq]
        have e68 : (k + 1) / 64 = 68 := by omega
        rw [e68]

theorem xorBlocks_sound {Cs : List (List (List Nat))} {M : List (List Nat)}
    (hl : ∀ C ∈ Cs, ∀ s < 69, lenL (lgetL C s) = rowsSn 4371 s)
    (h : ∀ s < 69, eqL (xorBlocks (rowsSn 4371 s) (Cs.map fun C => lgetL C s)) (lgetL M s) = true) :
    rowsMat 4371 (recOf M) = (Cs.map fun C => rowsMat 4371 (recOf C)).sum := by
  have hsum : ∀ (L : List (List (List Nat))) (i j : Fin 4371),
      (L.map fun C => rowsMat 4371 (recOf C)).sum i j =
        (L.map fun C => bz (((C.getD (i.val / 64) []).getD (i.val % 64) 0).testBit j.val)).sum := by
    intro L i j
    induction L with
    | nil => simp
    | cons C L ih =>
      rw [List.map_cons, List.sum_cons, Matrix.add_apply, ih, List.map_cons, List.sum_cons]
      change bz ((recOf C i.val).testBit j.val) + _ = _
      rw [recOf_eq]
  ext i j
  rw [hsum]
  change bz ((recOf M i.val).testBit j.val) = _
  have hs : i.val / 64 < 69 := by omega
  have e := eqL_eq _ _ (h _ hs)
  rw [recOf_eq, ← lgetL_eq, ← e]
  have hlen : ∀ B ∈ Cs.map (fun C => lgetL C (i.val / 64)), B.length = rowsSn 4371 (i.val / 64) := by
    intro B hB
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
    rw [← lenL_eq]
    exact hl C hC _ hs
  rw [(xorBlocks_spec _ j.val _ hlen).2, List.map_map]
  congr 1
  apply List.map_congr_left
  intro C _
  simp only [Function.comp, lgetL_eq]

theorem shapeOK_sound {M : List Nat} {k : Nat} (hM : wfMat M = true) (h : shapeOK M k = true) :
    LinearIndependent (ZMod 2) (fun i : {i : Fin 4370 // i.val < k} => stripMat M i) ∧
      ∀ i : Fin 4370, k ≤ i.val → stripMat M i = 0 := by
  rw [wfMat_eq] at hM
  have hl := (wf_bit hM).1
  have key : shapeOK M k = notB (Nat.beq ((List.range (64 * M.length)).foldl
      (fun st i => if Nat.blt i k then echStep (rowAt (SMn 4370) M i) st
        else if Nat.beq (rowAt (SMn 4370) M i) 0 then st else 0) topRow) 0) := by
    unfold shapeOK
    rw [foldRows_eq, fOuter_eq]
    congr 2
    apply foldl_ext
    intro x _ st
    simp only [Nat.zero_add, bool_rec_eq]
    rfl
  rw [key] at h
  have hne := notB_beq h
  refine ⟨ech_linIndep hl (fun i => Nat.blt i k) (fun _ r => Nat.beq r 0) _ hne (by norm_num)
    (fun i => i.val < k)
    (fun i hi => by rw [Nat.blt_eq]; exact hi), ?_⟩
  intro i hi
  obtain ⟨_, B, _, _⟩ := ech_fold (fun i => Nat.blt i k) (fun _ r => Nat.beq r 0)
    (rowAt (SMn 4370) M) topRow _ hne
  have := B i.val (by omega) (by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega)
  rw [Nat.beq_eq] at this
  exact stripMatG_row_zero this

theorem echFrom_sound {M : List Nat} {k : Nat} (hM : wfMat M = true) (h : echFrom M k = true) :
    LinearIndependent (ZMod 2) (fun i : {i : Fin 4370 // k ≤ i.val} => stripMat M i) := by
  rw [wfMat_eq] at hM
  have hl := (wf_bit hM).1
  have key : echFrom M k = notB (Nat.beq ((List.range (64 * M.length)).foldl
      (fun st i => if (Nat.ble k i && Nat.blt i 4370) then echStep (rowAt (SMn 4370) M i) st
        else if true then st else 0) topRow) 0) := by
    unfold echFrom
    rw [foldRows_eq, fOuter_eq]
    congr 2
    apply foldl_ext
    intro x _ st
    simp only [Nat.zero_add, bool_rec_eq]
    cases Nat.ble k x <;> cases Nat.blt x 4370 <;> rfl
  rw [key] at h
  exact ech_linIndep hl (fun i => Nat.ble k i && Nat.blt i 4370) (fun _ _ => true) _ (notB_beq h) (by norm_num) (fun i => k ≤ i.val)
    (fun i hi => by
      rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
      exact ⟨hi, i.isLt⟩)

theorem shapeOKn_sound {M : List Nat} {k : Nat} (hM : wfMatn 4371 M = true)
    (h : shapeOKn 4371 M k = true) :
    LinearIndependent (ZMod 2) (fun i : {i : Fin 4371 // i.val < k} => stripMatn M i) := by
  have hl := (wf_bit hM).1
  have key : shapeOKn 4371 M k = notB (Nat.beq ((List.range (64 * M.length)).foldl
      (fun st i => if Nat.blt i k then echStep (rowAt (SMn 4371) M i) st
        else if Nat.beq (rowAt (SMn 4371) M i) 0 then st else 0) topRow) 0) := by
    unfold shapeOKn
    rw [foldRowsn_eq, fOuter_eq]
    congr 2
    apply foldl_ext
    intro x _ st
    simp only [Nat.zero_add, bool_rec_eq]
    rfl
  rw [key] at h
  exact ech_linIndep hl (fun i => Nat.blt i k) (fun _ r => Nat.beq r 0) _ (notB_beq h)
    (by norm_num) (fun i => i.val < k)
    (fun i hi => by rw [Nat.blt_eq]; exact hi)

end CFSG.KC.BM.Fix

end
