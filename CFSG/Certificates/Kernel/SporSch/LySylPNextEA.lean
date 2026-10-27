module

public import CFSG.Certificates.Kernel.SporSch.LySylDefs
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Sporadic.Schreier.LyCheckSylow

public section

namespace CFSG.KS.SporSch.LySylP.NextEA

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LyM CFSG.Sporadic.LySchreier.Native
open CFSG.KS.SporSch.LySyl

private theorem testBit_maskL (E : List Nat) (i : Nat) :
    (maskL E).testBit i = decide (i ∈ E) := by
  induction E with
  | nil => exact Nat.zero_testBit i
  | cons x E ih =>
    change (maskL E ||| 1 <<< x).testBit i = _
    rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : i = x
    · subst h; simp
    · simp [h, Ne.symm h]

private theorem lenL_eq : ∀ E : List Nat, lenL E = E.length
  | [] => rfl
  | _ :: E => congrArg Nat.succ (lenL_eq E)

private noncomputable def incG : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih p => bAnd(Nat.ble p x, ih (Nat.succ x)))

private theorem incG_cons (x : Nat) (E : List Nat) (p : Nat) :
    incG (x :: E) p = (Nat.ble p x && incG E (x + 1)) := by
  rw [← CFSG.KS.Raw.Orb.bAnd_eq]
  rfl

private theorem incG_spec : ∀ (E : List Nat) (p : Nat), incG E p = true →
    (∀ x ∈ E, p ≤ x) ∧ E.Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | x :: E, p, h => by
    rw [incG_cons, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨h1, h2⟩ := incG_spec E (x + 1) h.2
    refine ⟨?_, List.pairwise_cons.2 ⟨fun y hy => h1 y hy, h2⟩⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · have := h1 y hy
      omega

private theorem incL_spec {E : List Nat} (h : incL E = true) : E.Pairwise (· < ·) :=
  (incG_spec E 0 h).2

private theorem allLtN_iff (n : Nat) :
    ∀ l : List Nat, CFSG.KS.Mathieu.allLtN n l = true ↔ ∀ x ∈ l, x < n
  | [] => by simp [CFSG.KS.Mathieu.allLtN]
  | x :: l => by
    change bAnd(Nat.blt x n, CFSG.KS.Mathieu.allLtN n l) = true ↔ _
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, allLtN_iff n l,
      List.forall_mem_cons]

private theorem eq_of_inc : ∀ {A B : List Nat}, A.Pairwise (· < ·) → B.Pairwise (· < ·) →
    (∀ a, a ∈ A ↔ a ∈ B) → A = B
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (List.mem_cons.2 (Or.inl rfl))) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).1 (List.mem_cons.2 (Or.inl rfl))) List.not_mem_nil
  | a :: A, b :: B, hA, hB, h => by
    rw [List.pairwise_cons] at hA hB
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 (List.mem_cons.2 (Or.inl rfl))) with e | e
      · exact e
      rcases List.mem_cons.1 ((h b).2 (List.mem_cons.2 (Or.inl rfl))) with e' | e'
      · exact e'.symm
      have := hA.1 b e'
      have := hB.1 a e
      omega
    subst hab
    rw [eq_of_inc hA.2 hB.2 fun x => ?_]
    constructor
    · intro hx
      have hne : x ≠ a := fun e => by have := hA.1 x hx; omega
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd e hne
      · exact e
    · intro hx
      have hne : x ≠ a := fun e => by have := hB.1 x hx; omega
      rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd e hne
      · exact e

private theorem eq_of_maskL {A B : List Nat} (hA : A.Pairwise (· < ·)) (hB : B.Pairwise (· < ·))
    (h : maskL A = maskL B) : A = B :=
  eq_of_inc hA hB fun a => by
    have := testBit_maskL A a
    rw [h, testBit_maskL B a] at this
    exact (decide_eq_decide.1 this).symm

private theorem nodup_of_len {R S : List Nat} (hR : R.Nodup) (hm : ∀ y, y ∈ R ↔ y ∈ S)
    (hl : R.length = S.length) : S.Nodup := by
  have hp : R.Perm S.dedup := (List.perm_ext_iff_of_nodup hR (List.nodup_dedup S)).2 fun y => by
    rw [List.mem_dedup]; exact hm y
  have e : S.dedup = S := (List.dedup_sublist S).eq_of_length (by rw [← hp.length_eq, hl])
  rw [← e]
  exact List.nodup_dedup S

private theorem tm_TBL {MT : Nat → Nat} {n i j : Nat} (hi : i < n) (hj : j < n) :
    tm (TBL MT n) i j = tmK MT i j := by
  unfold tm TBL
  rw [getElem!_pos (Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => tmK MT i.val j.val)
      i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos (Array.ofFn (n := n) fun j => tmK MT i j.val) j (by simpa using hj),
    Array.getElem_ofFn]

section Checks

variable {MT : Nat → Nat} {n : Nat} {E : List Nat}

private theorem extK_eq (hE : ∀ e ∈ E, e < n) {x : Nat} (hx : x < n) :
    extK MT n (maskL E) x = extendsBy (TBL MT n) E x := by
  rw [Bool.eq_iff_iff]
  unfold extK extendsBy isInv
  simp only [CFSG.KS.Raw.Orb.bAnd_eq]
  simp only [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.hasBit_eq, testBit_maskL,
    CFSG.KS.Raw.Orb.allN_iff, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    Nat.beq_eq, bne_iff_ne, beq_iff_eq, decide_eq_true_eq, ne_eq, List.contains_iff_mem,
    List.all_eq_true, tm_TBL hx hx]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨⟨⟨h0, h1⟩, h2⟩, fun e he => ?_⟩
    have := h3 e (hE e he)
    rw [if_pos he, Nat.beq_eq] at this
    rw [tm_TBL hx (hE e he), tm_TBL (hE e he) hx]
    exact this
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    refine ⟨h0, h1, h2, fun e he => ?_⟩
    split
    · next hm =>
      have := h3 e hm
      rw [tm_TBL hx (hE e hm), tm_TBL (hE e hm) hx] at this
      rw [Nat.beq_eq]
      exact this
    · rfl

private theorem spanM_fold (M x i : Nat) : ∀ l : List Nat,
    (l.foldr (fun e acc => if M.testBit e = true then acc ||| 2 ^ tmK MT x e else acc) M).testBit i
      = (M.testBit i || l.any fun e => M.testBit e && decide (tmK MT x e = i))
  | [] => by simp
  | e :: l => by
    rw [List.foldr_cons, List.any_cons]
    split
    · next h =>
      rw [Nat.testBit_or, spanM_fold M x i l, Nat.testBit_two_pow, h]
      cases M.testBit i <;> simp [Bool.or_comm]
    · next h =>
      rw [spanM_fold M x i l]
      simp only [Bool.not_eq_true] at h
      simp [h]

private theorem spanM_eq (hE : ∀ e ∈ E, e < n) {x : Nat} (hx : x < n) :
    spanM MT n (maskL E) x = maskL (spanBy (TBL MT n) E x) := by
  have e1 : spanM MT n (maskL E) x = (List.range n).foldr
      (fun e acc => if (maskL E).testBit e = true then acc ||| 2 ^ tmK MT x e else acc)
      (maskL E) := by
    unfold spanM
    rw [CFSG.KS.Raw.Orb.foldN_eq]
    congr 1
    funext e acc
    rw [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.hasBit_eq]
    split
    · exact congrArg (Nat.lor acc) (Nat.one_shiftLeft _)
    · rfl
  rw [e1]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [spanM_fold, testBit_maskL, testBit_maskL]
  unfold spanBy
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true,
    testBit_maskL, List.mem_range, (List.mergeSort_perm _ _).mem_iff, List.mem_append,
    List.mem_map]
  constructor
  · rintro (h | ⟨e, -, he, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, tm_TBL hx (hE e he)⟩
  · rintro (h | ⟨e, he, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, hE e he, he, (tm_TBL hx (hE e he)).symm⟩

private theorem popN_eq (M n : Nat) :
    popN M n = ((List.range n).filter fun i => M.testBit i).length := by
  unfold popN
  rw [CFSG.KS.Raw.Orb.foldN_eq]
  generalize List.range n = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.hasBit_eq, List.filter_cons]
    split <;> simp_all

end Checks

private theorem findM_spec (NM : Nat → Nat) (cnt m : Nat) :
    (findM NM cnt m < cnt → NM (findM NM cnt m) = m) ∧
      (¬ findM NM cnt m < cnt → ∀ i < cnt, NM i ≠ m) := by
  have key : ∀ (l : List Nat) (d : Nat),
      (l.foldr (fun i s => if NM i = m then i else s) d = d ∧ ∀ i ∈ l, NM i ≠ m) ∨
      (l.foldr (fun i s => if NM i = m then i else s) d ∈ l ∧
        NM (l.foldr (fun i s => if NM i = m then i else s) d) = m) := by
    intro l d
    induction l with
    | nil => exact Or.inl ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
    | cons a l ih =>
      rw [List.foldr_cons]
      by_cases ha : NM a = m
      · rw [if_pos ha]
        exact Or.inr ⟨List.mem_cons_self .., ha⟩
      · rw [if_neg ha]
        rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine Or.inl ⟨h1, fun i hi => ?_⟩
          rcases List.mem_cons.1 hi with rfl | hi
          · exact ha
          · exact h2 i hi
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
  have e : findM NM cnt m = (List.range cnt).foldr (fun i s => if NM i = m then i else s) cnt := by
    unfold findM
    rw [CFSG.KS.Raw.Orb.foldN_eq]
    congr 1
    funext i s
    rw [CFSG.KS.Raw.Orb.nIf_eq]
    simp only [Nat.beq_eq]
  rw [e]
  rcases key (List.range cnt) cnt with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]
    exact ⟨fun h => absurd h (Nat.lt_irrefl _), fun _ i hi => h2 i (List.mem_range.2 hi)⟩
  · exact ⟨fun _ => h2, fun h => absurd (List.mem_range.1 h1) h⟩

private noncomputable def eaStep (MT NM : Nat → Nat) (n nN M k x c : Nat) : Nat :=
  if 1048576 ≤ c then c else
  if extK MT n M x = true then
    (if popN (spanM MT n M x) n = k + k then
      (if findM NM c (spanM MT n M x) < c then c else
        if c < nN ∧ NM c = spanM MT n M x then c + 1 else 1048576)
    else 1048576)
  else c

private theorem eaOne_eq (MT NM : Nat → Nat) (n nN M k cnt : Nat) :
    eaOne MT NM n nN M k cnt = (List.range n).foldl (fun c x => eaStep MT NM n nN M k x c) cnt := by
  unfold eaOne
  rw [CFSG.KS.Raw.Orb.foldUp_eq]
  congr 1
  funext c x
  unfold eaStep
  simp only [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.strictN_eq, CFSG.KS.Raw.Orb.bAnd_eq,
    Nat.ble_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]
  rfl

section Replay

variable {MT NM : Nat → Nat} {n nN : Nat} {L' : List (List Nat)}

private def Good (nN : Nat) (L' : List (List Nat)) (P : List (List Nat)) (c : Nat) : Prop :=
  c < 1048576 → c ≤ nN ∧ P.eraseDups = L'.take c

private theorem mem_take_getD {c : Nat} (hc : c ≤ L'.length) {y : List Nat} :
    y ∈ L'.take c ↔ ∃ i < c, L'.getD i [] = y := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.length_take] at hi
    refine ⟨i, by omega, ?_⟩
    rw [List.getElem_take, List.getD_eq_getElem]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, by rw [List.length_take]; omega, ?_⟩
    rw [List.getElem_take, List.getD_eq_getElem]

private theorem take_succ_getD {c : Nat} (hc : c < L'.length) :
    L'.take (c + 1) = L'.take c ++ [L'.getD c []] := by
  rw [List.take_succ, List.getElem?_eq_getElem hc, List.getD_eq_getElem _ _ hc]
  rfl

private theorem eaStep_good (hrows : ∀ i < n, ∀ j < n, tmK MT i j < n) {E : List Nat}
    (hEi : E.Pairwise (· < ·)) (hE : ∀ e ∈ E, e < n) (hlen : L'.length = nN)
    (hNM : ∀ j < nN, listOfM (NM j) n (L'.getD j []) = true)
    {x : Nat} (hx : x < n) {P : List (List Nat)} {c : Nat} (hG : Good nN L' P c) :
    Good nN L' (P ++ if extendsBy (TBL MT n) E x = true then [spanBy (TBL MT n) E x] else [])
      (eaStep MT NM n nN (maskL E) (lenL E) x c) := by
  intro hlt
  unfold eaStep at hlt ⊢
  by_cases hc : 1048576 ≤ c
  · rw [if_pos hc] at hlt
    omega
  rw [if_neg hc] at hlt ⊢
  obtain ⟨hcN, hP⟩ := hG (by omega)
  rw [extK_eq hE hx] at hlt ⊢
  by_cases hext : extendsBy (TBL MT n) E x = true
  swap
  · rw [if_neg hext] at hlt
    rw [if_neg hext, if_neg hext, List.append_nil]
    exact ⟨hcN, hP⟩
  rw [if_pos hext] at hlt
  rw [if_pos hext, if_pos hext]
  rw [spanM_eq hE hx] at hlt ⊢
  set y := spanBy (TBL MT n) E x with hy
  by_cases hpop : popN (maskL y) n = lenL E + lenL E
  swap
  · rw [if_neg hpop] at hlt
    omega
  rw [if_pos hpop] at hlt ⊢
  set S := E ++ E.map (tm (TBL MT n) x ·) with hS
  have hSn : ∀ z ∈ S, z < n := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact hE z hz
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
      rw [tm_TBL hx (hE e he)]
      exact hrows x hx e (hE e he)
  have hyS : ∀ z, z ∈ y ↔ z ∈ S := fun z => (List.mergeSort_perm _ _).mem_iff
  have hSnd : S.Nodup := by
    refine nodup_of_len (R := (List.range n).filter fun i => (maskL y).testBit i)
      (List.nodup_range.filter _) (fun z => ?_) ?_
    · rw [List.mem_filter, testBit_maskL, decide_eq_true_eq, List.mem_range, hyS]
      exact ⟨fun h => h.2, fun h => ⟨hSn z h, h⟩⟩
    · rw [← popN_eq, hpop, lenL_eq, hS, List.length_append, List.length_map]
  have hyi : y.Pairwise (· < ·) := by
    have h1 : y.Pairwise (fun a b => decide (a ≤ b) = true) :=
      List.pairwise_mergeSort (fun a b c h1 h2 => by simp at *; omega)
        (fun a b => by simp; omega) _
    have h2 : y.Nodup := (List.mergeSort_perm _ _).nodup_iff.2 hSnd
    exact (h1.and h2).imp fun h => by simp at h; omega
  have hlistOf : ∀ j < nN, (L'.getD j []).Pairwise (· < ·) ∧ maskL (L'.getD j []) = NM j := by
    intro j hj
    have h := hNM j hj
    unfold listOfM at h
    rw [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
      Nat.beq_eq] at h
    exact ⟨incL_spec h.1, h.2.1⟩
  obtain ⟨hf1, hf2⟩ := findM_spec NM c (maskL y)
  by_cases hf : findM NM c (maskL y) < c
  · rw [if_pos hf]
    refine ⟨hcN, ?_⟩
    have hfN : findM NM c (maskL y) < nN := by omega
    obtain ⟨hi, hm⟩ := hlistOf _ hfN
    have hyf : L'.getD (findM NM c (maskL y)) [] = y := eq_of_maskL hi hyi (by rw [hm, hf1 hf])
    have hyP : y ∈ P := by
      rw [← List.mem_eraseDups, hP, mem_take_getD (by omega)]
      exact ⟨_, hf, hyf⟩
    rw [List.eraseDups_append, hP]
    simp [List.removeAll, hyP]
  · rw [if_neg hf] at hlt ⊢
    by_cases hnew : c < nN ∧ NM c = maskL y
    swap
    · rw [if_neg hnew] at hlt
      omega
    rw [if_pos hnew]
    refine ⟨hnew.1, ?_⟩
    obtain ⟨hi, hm⟩ := hlistOf c hnew.1
    have hyc : L'.getD c [] = y := eq_of_maskL hi hyi (by rw [hm, hnew.2])
    have hyP : y ∉ P := by
      intro hyP
      rw [← List.mem_eraseDups, hP, mem_take_getD (by omega)] at hyP
      obtain ⟨i, hi', hyi'⟩ := hyP
      apply hf2 hf i hi'
      rw [← (hlistOf i (by omega)).2, hyi']
    rw [List.eraseDups_append, hP, take_succ_getD (by omega), hyc]
    simp [List.removeAll, hyP, List.eraseDups_cons]

private theorem eaOne_good (hrows : ∀ i < n, ∀ j < n, tmK MT i j < n) {E : List Nat}
    (hEi : E.Pairwise (· < ·)) (hE : ∀ e ∈ E, e < n) (hlen : L'.length = nN)
    (hNM : ∀ j < nN, listOfM (NM j) n (L'.getD j []) = true) :
    ∀ (xs : List Nat), (∀ x ∈ xs, x < n) → ∀ (P : List (List Nat)) (c : Nat), Good nN L' P c →
      Good nN L' (P ++ (xs.filter (extendsBy (TBL MT n) E)).map (spanBy (TBL MT n) E))
        (xs.foldl (fun c x => eaStep MT NM n nN (maskL E) (lenL E) x c) c)
  | [], _, P, c, h => by simpa using h
  | x :: xs, hxs, P, c, h => by
    rw [List.foldl_cons]
    have h1 := eaStep_good hrows hEi hE hlen hNM (hxs x (List.mem_cons.2 (Or.inl rfl))) h
    have h2 := eaOne_good hrows hEi hE hlen hNM xs (fun z hz => hxs z (List.mem_cons_of_mem _ hz))
      _ _ h1
    rw [List.filter_cons]
    split
    · next hx => simpa [hx] using h2
    · next hx => simpa [hx] using h2

end Replay

theorem nextEA_sound {n nN : Nat} {MT NM : Nat → Nat} {L L' : List (List Nat)} {CT : Nat → Nat}
    (hn : n ≤ 256) (hrows : ∀ i < n, ∀ j < n, tmK MT i j < n)
    (hL : ∀ E ∈ L, incL E = true ∧ CFSG.KS.Mathieu.allLtN n E = true)
    (hrun : ∀ t < L.length, eaOne MT NM n nN (maskL (L.getD t [])) (lenL (L.getD t [])) (CT t) =
      CT (Nat.succ t))
    (hC0 : CT 0 = 0) (hCn : CT L.length = nN) (hnN : nN < 1048576) (hlen : L'.length = nN)
    (hNM : ∀ j < nN, listOfM (NM j) n (L'.getD j []) = true) :
    nextEA (TBL MT n) n L = L' ∧ extOK (TBL MT n) n L L' = true := by
  set G : List Nat → List (List Nat) := fun E =>
    ((List.range n).filter (extendsBy (TBL MT n) E)).map (spanBy (TBL MT n) E) with hG
  have hinv : ∀ t ≤ L.length, Good nN L' ((L.take t).flatMap G) (CT t) := by
    intro t
    induction t with
    | zero =>
      intro _ _
      rw [hC0]
      exact ⟨Nat.zero_le _, by simp⟩
    | succ t ih =>
      intro ht
      have htl : t < L.length := by omega
      have hmem : L.getD t [] ∈ L := by
        rw [List.getD_eq_getElem _ _ htl]
        exact List.getElem_mem htl
      obtain ⟨h1, h2⟩ := hL _ hmem
      have hE := (allLtN_iff n _).1 h2
      rw [← hrun t htl, eaOne_eq]
      have e : L.take (t + 1) = L.take t ++ [L.getD t []] := by
        rw [List.take_succ, List.getElem?_eq_getElem htl, List.getD_eq_getElem _ _ htl]
        rfl
      rw [e, List.flatMap_append, List.flatMap_singleton]
      exact eaOne_good hrows (incL_spec h1) hE hlen hNM (List.range n)
        (fun x hx => List.mem_range.1 hx) _ _ (ih (by omega))
  have hF := hinv L.length (le_refl _) (by rw [hCn]; exact hnN)
  rw [List.take_length, hCn, ← hlen, List.take_length] at hF
  have hnext : nextEA (TBL MT n) n L = L' := hF.2
  refine ⟨hnext, ?_⟩
  unfold extOK
  rw [List.all_eq_true]
  intro E hE
  rw [List.all_eq_true]
  intro x hx
  rw [Bool.or_eq_true, Bool.not_eq_true']
  by_cases hext : extendsBy (TBL MT n) E x = true
  · refine Or.inr ?_
    rw [← hnext, List.contains_iff_mem]
    unfold nextEA
    rw [List.mem_eraseDups, List.mem_flatMap]
    exact ⟨E, hE, List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, hext⟩, rfl⟩⟩
  · exact Or.inl (by simpa using hext)

end CFSG.KS.SporSch.LySylP.NextEA

end
