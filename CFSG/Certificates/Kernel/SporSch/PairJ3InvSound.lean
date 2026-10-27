module

public import Certificates.Data.Kernel.SporSch.PairJ3Faith
public import CFSG.Sporadic.Schreier.PairF2Sep

public section

namespace CFSG.KS.SporSch.PF2

open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.SmallF2.Native CFSG.KLie.CT CFSG.KC.M1F2

@[expose] noncomputable def unpackP (d M : Nat) : Array Nat :=
  Array.ofFn (n := d) fun i => rowF d M i.val

@[expose] def pivA (d c : Nat) (a : Array Nat) : Nat :=
  (List.range' c (d - c)).foldl (fun piv i => if (piv == d && a[i]!.testBit c) = true then i else piv) d

@[expose] def elimStepA (c ap rp : Nat) (s : Array Nat × Array Nat) (i : Nat) :
    Array Nat × Array Nat :=
  if (i != c && s.1[i]!.testBit c) = true then
    (s.1.set! i (s.1[i]! ^^^ ap), s.2.set! i (s.2[i]! ^^^ rp)) else (s.1, s.2)

@[expose] def elimA (d c ap rp : Nat) (s : Array Nat × Array Nat) : Array Nat × Array Nat :=
  (List.range' 0 d).foldl (elimStepA c ap rp) s

@[expose] def colA (d c : Nat) (s : Array Nat × Array Nat) : Array Nat × Array Nat :=
  if pivA d c s.1 < d then
    elimA d c s.1[pivA d c s.1]! s.2[pivA d c s.1]!
      ((s.1.set! (pivA d c s.1) s.1[c]!).set! c s.1[pivA d c s.1]!,
        (s.2.set! (pivA d c s.1) s.2[c]!).set! c s.2[pivA d c s.1]!)
  else (s.1, s.2)

theorem ite_yield {β : Type} {C : Prop} [Decidable C] (x y : β) :
    (if C then (pure (ForInStep.yield x) : Id (ForInStep β)) else pure (ForInStep.yield y)) =
      pure (ForInStep.yield (if C then x else y)) := by
  split <;> rfl

theorem invRowsF2_fold (d : Nat) (M : Array Nat) :
    invRowsF2 d M = ((List.range' 0 d).foldl (fun s c => colA d c s) (M, idRows d)).2 := by
  unfold invRowsF2 colA pivA elimA
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, ite_yield,
    List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

@[expose] def pivP (d c : Nat) (L : List (Nat × Nat)) : Nat :=
  (List.range' c (d - c)).foldl
    (fun piv i => if (piv == d && (L.getD i (0, 0)).1.testBit c) = true then i else piv) d

@[expose] def elimF (c ap rp j : Nat) (p : Nat × Nat) : Nat × Nat :=
  if (j != c && p.1.testBit c) = true then (p.1 ^^^ ap, p.2 ^^^ rp) else p

@[expose] def elimStepP (c ap rp : Nat) (L : List (Nat × Nat)) (i : Nat) : List (Nat × Nat) :=
  L.set i (elimF c ap rp i (L.getD i (0, 0)))

@[expose] def elimP (d c ap rp : Nat) (L : List (Nat × Nat)) : List (Nat × Nat) :=
  (List.range' 0 d).foldl (elimStepP c ap rp) L

@[expose] def colP (d c : Nat) (L : List (Nat × Nat)) : List (Nat × Nat) :=
  if pivP d c L < d then
    elimP d c (L.getD (pivP d c L) (0, 0)).1 (L.getD (pivP d c L) (0, 0)).2
      ((L.set (pivP d c L) (L.getD c (0, 0))).set c (L.getD (pivP d c L) (0, 0)))
  else L

theorem arr_get (a : Array Nat) (i : Nat) : a[i]! = a.toList.getD i 0 := by
  rcases a with ⟨l⟩
  simp only [getElem!_def, List.getD_eq_getElem?_getD, List.getElem?_toArray]
  cases l[i]? <;> rfl

theorem zip_getD (l1 l2 : List Nat) (h : l1.length = l2.length) (i : Nat) :
    (List.zip l1 l2).getD i (0, 0) = (l1.getD i 0, l2.getD i 0) := by
  induction l1 generalizing l2 i with
  | nil => cases l2 <;> simp_all
  | cons x l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons y l2 =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih l2 (by simpa using h) i

theorem zip_set (l1 l2 : List Nat) (i x y : Nat) :
    List.zip (l1.set i x) (l2.set i y) = (List.zip l1 l2).set i (x, y) := by
  induction l1 generalizing l2 i with
  | nil => simp
  | cons a l1 ih =>
    cases l2 with
    | nil => cases i <;> simp
    | cons b l2 =>
      cases i with
      | zero => simp
      | succ i => simp [ih]

theorem arr_set (a : Array Nat) (i x : Nat) : (a.set! i x).toList = a.toList.set i x := by
  rcases a with ⟨l⟩
  simp only [Array.set!, Array.setIfInBounds]
  split
  · simp
  · rename_i h
    simp only [List.size_toArray, not_lt] at h
    simp [List.set_eq_of_length_le h]

theorem set_getD_self (L : List (Nat × Nat)) (i : Nat) : L.set i (L.getD i (0, 0)) = L := by
  induction L generalizing i with
  | nil => simp
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ i => simp only [List.getD_cons_succ, List.set_cons_succ, ih]

@[expose] def zA (s : Array Nat × Array Nat) : List (Nat × Nat) := List.zip s.1.toList s.2.toList

theorem zA_getD (s : Array Nat × Array Nat) (h : s.1.size = s.2.size) (i : Nat) :
    (zA s).getD i (0, 0) = (s.1[i]!, s.2[i]!) := by
  rw [zA, zip_getD _ _ (by simpa using h), arr_get, arr_get]

theorem zA_set (s : Array Nat × Array Nat) (i x y : Nat) :
    zA (s.1.set! i x, s.2.set! i y) = (zA s).set i (x, y) := by
  simp only [zA, arr_set, zip_set]

theorem pivA_eq (d c : Nat) (s : Array Nat × Array Nat) (h : s.1.size = s.2.size) :
    pivA d c s.1 = pivP d c (zA s) := by
  unfold pivA pivP
  congr 1
  funext piv i
  rw [zA_getD s h]

theorem elimStep_eq (c ap rp i : Nat) (s : Array Nat × Array Nat) (h : s.1.size = s.2.size) :
    zA (elimStepA c ap rp s i) = elimStepP c ap rp (zA s) i ∧
      (elimStepA c ap rp s i).1.size = (elimStepA c ap rp s i).2.size := by
  unfold elimStepA elimStepP elimF
  rw [zA_getD s h]
  by_cases hc : (i != c && s.1[i]!.testBit c) = true
  · simp only [hc, ite_true]
    exact ⟨zA_set s i _ _, by simp [h]⟩
  · simp only [hc, ite_false, Bool.false_eq_true]
    refine ⟨?_, h⟩
    rw [← zA_getD s h, set_getD_self]

theorem elimA_eq (d c ap rp : Nat) (s : Array Nat × Array Nat) (h : s.1.size = s.2.size) :
    zA (elimA d c ap rp s) = elimP d c ap rp (zA s) ∧
      (elimA d c ap rp s).1.size = (elimA d c ap rp s).2.size := by
  unfold elimA elimP
  generalize List.range' 0 d = l
  induction l generalizing s with
  | nil => exact ⟨rfl, h⟩
  | cons i l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := elimStep_eq c ap rp i s h
    rw [← h1]
    exact ih _ h2

theorem colA_eq (d c : Nat) (s : Array Nat × Array Nat) (h : s.1.size = s.2.size) :
    zA (colA d c s) = colP d c (zA s) ∧ (colA d c s).1.size = (colA d c s).2.size := by
  unfold colA colP
  rw [← pivA_eq d c s h]
  split
  · have hs : zA ((s.1.set! (pivA d c s.1) s.1[c]!).set! c s.1[pivA d c s.1]!,
        (s.2.set! (pivA d c s.1) s.2[c]!).set! c s.2[pivA d c s.1]!) =
        ((zA s).set (pivA d c s.1) ((zA s).getD c (0, 0))).set c
          ((zA s).getD (pivA d c s.1) (0, 0)) := by
      rw [zA_getD s h, zA_getD s h, ← zA_set s, ← zA_set]
    have hsz : ((s.1.set! (pivA d c s.1) s.1[c]!).set! c s.1[pivA d c s.1]!).size =
        ((s.2.set! (pivA d c s.1) s.2[c]!).set! c s.2[pivA d c s.1]!).size := by simp [h]
    obtain ⟨e1, e2⟩ := elimA_eq d c s.1[pivA d c s.1]! s.2[pivA d c s.1]!
      ((s.1.set! (pivA d c s.1) s.1[c]!).set! c s.1[pivA d c s.1]!,
        (s.2.set! (pivA d c s.1) s.2[c]!).set! c s.2[pivA d c s.1]!) hsz
    refine ⟨?_, e2⟩
    rw [e1, hs, zA_getD s h (pivA d c s.1)]
  · exact ⟨rfl, h⟩

theorem fold_colA_eq (d : Nat) (l : List Nat) (s : Array Nat × Array Nat) (h : s.1.size = s.2.size) :
    zA (l.foldl (fun s c => colA d c s) s) = l.foldl (fun L c => colP d c L) (zA s) ∧
      (l.foldl (fun s c => colA d c s) s).1.size = (l.foldl (fun s c => colA d c s) s).2.size := by
  induction l generalizing s with
  | nil => exact ⟨rfl, h⟩
  | cons c l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := colA_eq d c s h
    rw [← h1]
    exact ih _ h2

theorem bit_eq (X i : Nat) : bit X i = X.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff, Nat.beq_eq,
    decide_eq_true_iff]

theorem strictL_eq (y : Nat) (k : Nat → List (Nat × Nat)) : strictL y k = k y := by
  cases y <;> rfl

theorem getPK_eq (L : List (Nat × Nat)) (i : Nat) : getPK L i = L.getD i (0, 0) := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem setPK_eq (L : List (Nat × Nat)) (i : Nat) (p : Nat × Nat) : setPK L i p = L.set i p := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (x :: ·) (ih i)

theorem cond_eq (i c a : Nat) :
    Bool.rec (motive := fun _ => Bool) false (bit a c)
      (Bool.rec (motive := fun _ => Bool) true false (Nat.beq i c)) = (i != c && a.testBit c) := by
  rw [bit_eq]
  cases h : Nat.beq i c
  · have : i ≠ c := fun e => by simp [e] at h
    simp [this]
  · have : i = c := Nat.eq_of_beq_eq_true h
    simp [this]

theorem elimGo_eq (c ap rp : Nat) (L : List (Nat × Nat)) (i : Nat) :
    elimGo c ap rp L i = L.mapIdx (fun j p => elimF c ap rp (i + j) p) := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨a, r⟩ := x
    rw [List.mapIdx_cons]
    change Bool.rec (motive := fun _ => List (Nat × Nat)) ((a, r) :: elimGo c ap rp L (i + 1))
        ((Nat.xor a ap, Nat.xor r rp) :: elimGo c ap rp L (i + 1))
        (Bool.rec (motive := fun _ => Bool) false (bit a c)
          (Bool.rec (motive := fun _ => Bool) true false (Nat.beq i c))) = _
    rw [cond_eq, ih]
    have e : (fun j p => elimF c ap rp (i + (j + 1)) p) = fun j p => elimF c ap rp (i + 1 + j) p := by
      funext j p
      rw [Nat.add_comm j 1, Nat.add_assoc]
    rw [e]
    unfold elimF
    cases (i != c && a.testBit c) <;> rfl

theorem elimP_eq (c ap rp : Nat) (L : List (Nat × Nat)) :
    elimP L.length c ap rp L = L.mapIdx (fun j p => elimF c ap rp j p) := by
  have key : ∀ k, k ≤ L.length → (List.range' 0 k).foldl (elimStepP c ap rp) L =
      L.mapIdx (fun j p => if j < k then elimF c ap rp j p else p) := by
    intro k
    induction k with
    | zero =>
      intro _
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp
    | succ k ih =>
      intro hk
      rw [List.range'_concat, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      simp only [Nat.zero_add, Nat.one_mul]
      have hkL : k < L.length := by omega
      have hg : (L.mapIdx (fun j p => if j < k then elimF c ap rp j p else p)).getD k (0, 0) =
          L[k] := by
        rw [List.getD_eq_getElem _ _ (by simpa using hkL), List.getElem_mapIdx]
        simp
      unfold elimStepP
      rw [hg]
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.getElem_set, List.getElem_mapIdx]
      by_cases hj : k = j
      · subst hj
        simp
      · simp only [hj, ite_eq_right, not_false_eq_true]
        by_cases h3 : j < k
        · simp [h3, show j < k + 1 by omega]
        · simp [h3, show ¬ j < k + 1 by omega]
  unfold elimP
  rw [key L.length le_rfl]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_mapIdx]
  rw [ite_eq_left (by simpa using h1)]

theorem elimK_eq (c ap rp : Nat) (L : List (Nat × Nat)) :
    elimK c ap rp L = elimP L.length c ap rp L := by
  rw [elimP_eq, elimK, elimGo_eq]
  simp only [Nat.zero_add]

@[expose] def stepQ (d c : Nat) (L : List (Nat × Nat)) (piv j : Nat) : Nat :=
  if (piv == d && (decide (c ≤ j) && (L.getD j (0, 0)).1.testBit c)) = true then j else piv

theorem stepQ_keep (d c : Nat) (L : List (Nat × Nat)) (l : List Nat) (piv : Nat) (h : piv ≠ d) :
    l.foldl (stepQ d c L) piv = piv := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons]
    have : stepQ d c L piv j = piv := by
      unfold stepQ
      simp [h]
    rw [this, ih]

theorem pivGo_eq (d c : Nat) (L : List (Nat × Nat)) (hL : L.length ≤ d) :
    ∀ n i, i + n = L.length → pivGo d c (L.drop i) i = (List.range' i n).foldl (stepQ d c L) d := by
  intro n
  induction n with
  | zero =>
    intro i hi
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ n ih =>
    intro i hi
    have hiL : i < L.length := by omega
    rw [List.drop_eq_getElem_cons hiL, List.range'_succ, List.foldl_cons]
    rcases hx : L[i] with ⟨a, r⟩
    have hg : L.getD i (0, 0) = (a, r) := by rw [List.getD_eq_getElem _ _ hiL, hx]
    change Bool.rec (motive := fun _ => Nat) (pivGo d c (L.drop (i + 1)) (i + 1)) i
        (Bool.rec (motive := fun _ => Bool) false (bit a c) (Nat.ble c i)) = _
    rw [ih (i + 1) (by omega), bit_eq]
    have hs : stepQ d c L d i = if (decide (c ≤ i) && a.testBit c) = true then i else d := by
      unfold stepQ
      rw [hg]
      simp
    rw [hs]
    by_cases hq : (decide (c ≤ i) && a.testBit c) = true
    · have h1 : Nat.ble c i = true := by rw [Nat.ble_eq]; simp_all
      have h2 : a.testBit c = true := by simp_all
      rw [ite_eq_left hq, h1, h2]
      exact (stepQ_keep d c L _ i (by omega)).symm
    · have : (Bool.rec (motive := fun _ => Bool) false (a.testBit c) (Nat.ble c i)) = false := by
        cases h : Nat.ble c i
        · rfl
        · have := Nat.le_of_ble_eq_true h
          simp_all
      rw [this, ite_eq_right hq]

theorem foldl_congr_mem {f g : Nat → Nat → Nat} (l : List Nat) (h : ∀ j ∈ l, ∀ x, f x j = g x j)
    (x : Nat) : l.foldl f x = l.foldl g x := by
  induction l generalizing x with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [h j (List.mem_cons_self ..)]
    exact ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) _

theorem pivK_eq (d c : Nat) (L : List (Nat × Nat)) (hL : L.length = d) (hc : c ≤ d) :
    pivK d c L = pivP d c L := by
  unfold pivK
  have := pivGo_eq d c L hL.le d 0 (by omega)
  rw [List.drop_zero] at this
  rw [this]
  unfold pivP
  have hsplit : List.range' 0 d = List.range' 0 c ++ List.range' (0 + c) (d - c) := by
    rw [List.range'_append_1]
    congr 1
    omega
  rw [hsplit, List.foldl_append, Nat.zero_add]
  have h0 : (List.range' 0 c).foldl (stepQ d c L) d = d := by
    rw [foldl_congr_mem (g := fun x _ => x) (List.range' 0 c) (fun j hj x => by
      have : j < c := by simp at hj; omega
      unfold stepQ
      simp [show ¬ c ≤ j by omega])]
    clear hsplit
    induction (List.range' 0 c) <;> simp_all
  rw [h0]
  apply foldl_congr_mem
  intro j hj x
  have : c ≤ j := by simp at hj; omega
  unfold stepQ
  simp [this]

theorem colK_eq (d c : Nat) (L : List (Nat × Nat)) (hL : L.length = d) (hc : c ≤ d) :
    colK d c L = colP d c L := by
  unfold colK colP
  rw [strictL_eq, pivK_eq d c L hL hc]
  cases h : Nat.blt (pivP d c L) d
  · have : ¬ pivP d c L < d := by
      intro h'
      have : Nat.blt (pivP d c L) d = true := by rw [Nat.blt_eq]; exact h'
      simp_all
    rw [ite_eq_right this]
  · have : pivP d c L < d := by rw [← Nat.blt_eq]; exact h
    rw [ite_eq_left this]
    rw [getPK_eq, getPK_eq]
    rcases (L.getD (pivP d c L) (0, 0)) with ⟨ap, rp⟩
    change elimK c ap rp (setPK (setPK L _ _) c (ap, rp)) = _
    rw [setPK_eq, setPK_eq, elimK_eq]
    simp [hL]

theorem colP_length (d c : Nat) (L : List (Nat × Nat)) : (colP d c L).length = L.length := by
  unfold colP elimP
  split
  · have : ∀ (ap rp : Nat) (l : List Nat) (L' : List (Nat × Nat)),
        (l.foldl (elimStepP c ap rp) L').length = L'.length := by
      intro ap rp l
      induction l with
      | nil => intro _; rfl
      | cons j l ih =>
        intro L'
        rw [List.foldl_cons, ih]
        simp [elimStepP]
    rw [this]
    simp
  · rfl

theorem fold_colK_eq (d : Nat) (L : List (Nat × Nat)) (hL : L.length = d) :
    ∀ n c, c + n = d → (List.range' c n).foldl (fun L c => colK d c L) L =
      (List.range' c n).foldl (fun L c => colP d c L) L := by
  intro n
  induction n generalizing L with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro c hc
    rw [List.range'_succ, List.foldl_cons, List.foldl_cons, colK_eq d c L hL (by omega)]
    exact ih _ (by rw [colP_length, hL]) (c + 1) (by omega)

theorem eqLK_sound : ∀ {L L' : List (Nat × Nat)}, eqLK L L' = true → L = L'
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | (a, b) :: L, (a', b') :: L', h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (eqLK L L') (Nat.beq b b')) (Nat.beq a a') = true at h
    cases h1 : Nat.beq a a' <;> cases h2 : Nat.beq b b' <;> rw [h1, h2] at h <;>
      try exact absurd h Bool.false_ne_true
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, eqLK_sound h]

theorem initGo_eq (d M : Nat) : ∀ n k, initGo d M n k =
    (List.range' k n).map fun i => (rowF d M i, pw2 i) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih => intro k; rw [List.range'_succ, List.map_cons, ← ih]; rfl

theorem initK_eq (d M : Nat) :
    initK d M = List.zip (unpackP d M).toList (idRows d).toList := by
  rw [initK, initGo_eq]
  apply List.ext_getElem (by simp [unpackP, idRows])
  intro j h1 h2
  simp [unpackP, idRows, pw2, Nat.shiftLeft_eq]

theorem finGo_sound (d X : Nat) : ∀ (L : List (Nat × Nat)) (i : Nat), finGo d X L i = true →
    L.map Prod.snd = (List.range' i L.length).map (rowF d X) ∧ i + L.length = d := by
  intro L
  induction L with
  | nil => intro i h; exact ⟨rfl, by simpa using Nat.eq_of_beq_eq_true h⟩
  | cons p L ih =>
    intro i h
    obtain ⟨a, r⟩ := p
    change Bool.rec (motive := fun _ => Bool) false (finGo d X L (i + 1)) (Nat.beq r (rowF d X i))
      = true at h
    cases h1 : Nat.beq r (rowF d X i) <;> rw [h1] at h
    · exact absurd h Bool.false_ne_true
    · obtain ⟨e1, e2⟩ := ih (i + 1) h
      refine ⟨?_, by simp; omega⟩
      rw [List.length_cons, List.range'_succ, List.map_cons, List.map_cons, e1,
        Nat.eq_of_beq_eq_true h1]

theorem run_step {d c n : Nat} {L L' R : List (Nat × Nat)} (h : eqLK (colK d c L) L' = true)
    (h' : (List.range' (c + 1) n).foldl (fun L c => colK d c L) L' = R) :
    (List.range' c (n + 1)).foldl (fun L c => colK d c L) L = R := by
  rw [List.range'_succ, List.foldl_cons, eqLK_sound h, h']

theorem invRowsF2_unpack {d M X : Nat} {L R : List (Nat × Nat)} (h0 : eqLK (initK d M) L = true)
    (hrun : (List.range' 0 d).foldl (fun L c => colK d c L) L = R) (hR : finK d X R = true) :
    invRowsF2 d (unpackP d M) = unpackP d X := by
  have hf : finK d X ((List.range' 0 d).foldl (fun L c => colK d c L) L) = true := by rw [hrun]; exact hR
  have hL := eqLK_sound h0
  have hz : zA (unpackP d M, idRows d) = L := by rw [← hL, initK_eq]; rfl
  have hlen : L.length = d := by rw [← hz]; simp [zA, unpackP, idRows]
  have hA := fold_colA_eq d (List.range' 0 d) (unpackP d M, idRows d) (by simp [unpackP, idRows])
  rw [fold_colK_eq d L hlen d 0 (by omega), ← hz, ← hA.1] at hf
  rw [invRowsF2_fold]
  have hsz := hA.2
  generalize (List.range' 0 d).foldl (fun s c => colA d c s) (unpackP d M, idRows d) = s at hf hsz
  obtain ⟨e1, e2⟩ := finGo_sound d X _ 0 hf
  apply Array.ext'
  have hs2 : s.2.toList = (zA s).map Prod.snd := (List.map_snd_zip (by simp [hsz])).symm
  rw [hs2, e1]
  apply List.ext_getElem (by simp [unpackP]; simpa using e2)
  intro j h1 h2
  simp [unpackP]

end CFSG.KS.SporSch.PF2

end
