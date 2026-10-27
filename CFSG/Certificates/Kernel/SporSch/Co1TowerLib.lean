module

public import Certificates.Data.Kernel.SporSch.Co1Tower
public import CFSG.Sporadic.Schreier.Co1ChainCheck
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Std.Data.HashSet.Lemmas

namespace CFSG.KS.SporSch.VOrb.TowerLib

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.KS.Raw
  CFSG.KS.SporSch.M24 CFSG.KS.Mathieu

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem foldBlk_succ (b : Nat) (f : Nat → Nat → Nat) (l s : Nat) :
    foldBlk b f (l + 1) s = foldBlk b f l (f (b + l) s) := by
  have e : foldBlk b f (l + 1) s = strictN (f (b + l) s) (foldBlk b f l) := rfl
  rw [e, strictN_eq]

theorem foldBlk_eq (b : Nat) (f : Nat → Nat → Nat) (len s : Nat) :
    foldBlk b f len s = (List.range len).foldr (fun l s => f (b + l) s) s := by
  induction len generalizing s with
  | zero => rfl
  | succ len ih =>
    rw [foldBlk_succ, ih, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]

theorem foldr_range_add (f : Nat → Nat → Nat) (a b s : Nat) :
    (List.range (a + b)).foldr f s =
      (List.range a).foldr f ((List.range b).foldr (fun l s => f (a + l) s) s) := by
  rw [List.range_add, List.foldr_append, List.foldr_map]

theorem shiftLeft_six (x : Nat) : Nat.shiftLeft x (nat_lit 6) = x * 64 := by
  change x <<< 6 = x * 64
  rw [Nat.shiftLeft_eq]

theorem shiftRight_six (n : Nat) : Nat.shiftRight n (nat_lit 6) = n / 64 :=
  Nat.shiftRight_eq_div_pow n 6

theorem land_63 (n : Nat) : Nat.land n (nat_lit 63) = n % 64 :=
  Nat.and_two_pow_sub_one_eq_mod n 6

theorem foldN_rec_eq (f : Nat → Nat → Nat) (h : Nat) : ∀ x : Nat,
    Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) h x
      = (List.range (h * 64)).foldr f x := by
  induction h with
  | zero => intro x; rfl
  | succ h ih =>
    intro x
    have hs : Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
        (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
        (h + 1) x
        = strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) x)
            (Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
              (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
              h) :=
      rfl
    have e : (h + 1) * 64 = h * 64 + 64 := by omega
    rw [hs, strictN_eq, ih, foldBlk_eq, shiftLeft_six h, e, foldr_range_add f (h * 64) 64 x]

theorem foldN_eq (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = (List.range n).foldr f s := by
  refine Eq.trans (foldN_rec_eq f (Nat.shiftRight n (nat_lit 6))
    (foldBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) s)) ?_
  have e : n / 64 * 64 + n % 64 = n := by omega
  rw [foldBlk_eq, shiftLeft_six, land_63, shiftRight_six,
    ← foldr_range_add f (n / 64 * 64) (n % 64) s, e]

theorem foldr_range_succ (h : Nat → Nat → Nat) (k s : Nat) :
    (List.range (k + 1)).foldr h s =
      h 0 ((List.range k).foldr (fun x y => h (Nat.succ x) y) s) := by
  rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]

theorem foldr_rev_eq_foldl (g : Nat → Nat → Nat) (n : Nat) : ∀ s : Nat,
    (List.range n).foldr (fun i s => g (n - 1 - i) s) s
      = (List.range n).foldl (fun s i => g i s) s := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    have hf : (fun (x : Nat) (y : Nat) => g (n + 1 - 1 - Nat.succ x) y)
        = (fun (x : Nat) (y : Nat) => g (n - 1 - x) y) := by
      funext x y
      congr 1
      omega
    rw [foldr_range_succ, hf, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih s, Nat.sub_zero, Nat.add_sub_cancel]

theorem foldUp_eq (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldUp n f s = (List.range n).foldl (fun s i => f i s) s :=
  (foldN_eq n (fun i s => f (Nat.sub (Nat.sub n (nat_lit 1)) i) s) s).trans
    (foldr_rev_eq_foldl f n s)

theorem all_range_add (f : Nat → Bool) (a b : Nat) :
    (List.range (a + b)).all f
      = ((List.range a).all f && (List.range b).all fun l => f (a + l)) := by
  simp only [List.range_add, List.all_append, List.all_map, Function.comp_def]

theorem allBlk_eq (b : Nat) (f : Nat → Bool) (len : Nat) :
    allBlk b f len = (List.range len).all fun l => f (b + l) := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have hs : allBlk b f (len + 1) = (f (b + len) && allBlk b f len) := rfl
    rw [hs, List.range_succ, List.all_append, ← ih, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_comm]

theorem allN_rec_eq (f : Nat → Bool) (h : Nat) :
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) h
      = (List.range (h * 64)).all f := by
  induction h with
  | zero => rfl
  | succ h ih =>
    have hs : Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (h + 1)
        = (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) &&
            Nat.rec (motive := fun _ => Bool) true
              (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
                (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) h) :=
      rfl
    have e : (h + 1) * 64 = h * 64 + 64 := by omega
    rw [hs, ih, allBlk_eq, shiftLeft_six h, e, all_range_add f (h * 64) 64, Bool.and_comm]

theorem allN_eq (n : Nat) (f : Nat → Bool) : allN n f = (List.range n).all f := by
  have hs : allN n f = (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) &&
        Nat.rec (motive := fun _ => Bool) true
          (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
            (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64)))
          (Nat.shiftRight n (nat_lit 6))) :=
    rfl
  have e : n / 64 * 64 + n % 64 = n := by omega
  rw [hs, allN_rec_eq, allBlk_eq, shiftLeft_six, land_63, shiftRight_six, Bool.and_comm,
    ← all_range_add f (n / 64 * 64) (n % 64), e]

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  rw [allN_eq, List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.2 hi), fun h x hx => h x (List.mem_range.1 hx)⟩

theorem nget_eq (l : List Nat) (i : Nat) : nget l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change nget l i = _
      rw [ih]
      simp

theorem allLtN_iff (K : Nat) (l : List Nat) : allLtN K l = true ↔ ∀ x ∈ l, x < K := by
  induction l with
  | nil => simp [allLtN]
  | cons x l ih =>
    have e : allLtN K (x :: l) = (Nat.blt x K && allLtN K l) := bAnd_eq _ _
    simp [e, ih, Nat.blt_eq]

theorem fixesK_iff (M : Nat → Nat) (gens bs : List Nat) (k : Nat) :
    fixesK M gens bs k = true ↔ ∀ j ∈ gens, ∀ l < k, actK (M j) (bs.getD l 0) = bs.getD l 0 := by
  induction gens with
  | nil => simp [fixesK]
  | cons j gs ih =>
    have e : fixesK M (j :: gs) bs k =
        (allN k (fun l => strictB (nget bs l) (fun b => Nat.beq (actK (M j) b) b)) &&
          fixesK M gs bs k) := bAnd_eq _ _
    simp only [e, Bool.and_eq_true, allN_iff, strictB_eq, nget_eq, Nat.beq_eq, ih,
      List.mem_cons, forall_eq_or_imp]

def xs (f : Nat → Bool) (l : List Nat) : Bool := l.foldr (fun j b => f j ^^ b) false

theorem xs_nil (f : Nat → Bool) : xs f [] = false := rfl

theorem xs_cons (f : Nat → Bool) (a : Nat) (l : List Nat) : xs f (a :: l) = (f a ^^ xs f l) := rfl

theorem xs_append (f : Nat → Bool) (l₁ l₂ : List Nat) : xs f (l₁ ++ l₂) = (xs f l₁ ^^ xs f l₂) := by
  induction l₁ with
  | nil => simp [xs_nil]
  | cons a l ih => rw [List.cons_append, xs_cons, xs_cons, ih, Bool.xor_assoc]

theorem xs_map (f : Nat → Bool) (g : Nat → Nat) (l : List Nat) :
    xs f (l.map g) = xs (fun k => f (g k)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, xs_cons, xs_cons, ih]

theorem xs_xor (f g : Nat → Bool) (l : List Nat) :
    xs (fun k => f k ^^ g k) l = (xs f l ^^ xs g l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [xs_cons, xs_cons, xs_cons, ih]
    cases f a <;> cases g a <;> cases xs f l <;> cases xs g l <;> rfl

theorem xs_congr {f g : Nat → Bool} {l : List Nat} (h : ∀ j ∈ l, f j = g j) : xs f l = xs g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [xs_cons, xs_cons, h a (List.mem_cons_self ..),
      ih fun j hj => h j (List.mem_cons_of_mem a hj)]

theorem xs_false (l : List Nat) : xs (fun _ => false) l = false := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [xs_cons, ih]; rfl

def sx (x s : Nat) : Nat := x ^^^ x >>> s

theorem xs_sx (x s t : Nat) (ht : t = s + s) :
    xs (fun k => (sx x s).testBit k) (List.range s) = xs (fun k => x.testBit k) (List.range t) := by
  subst ht
  rw [List.range_add, xs_append, xs_map]
  simp only [sx, Nat.testBit_xor, Nat.testBit_shiftRight]
  exact xs_xor _ _ _

theorem parK_eq (x : Nat) : M24.parK x = sx (sx (sx (sx (sx x 16) 8) 4) 2) 1 &&& 1 := by
  simp only [M24.parK, strictN_eq]
  rfl

theorem and_one_beq (y : Nat) : Nat.beq (y &&& 1) 1 = y.testBit 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> rw [h] <;> rfl

theorem parK_and (r v : Nat) (hr : r < 2 ^ 24) :
    Nat.beq (M24.parK (Nat.land r v)) 1 =
      xs (fun j => r.testBit j && v.testBit j) (List.range 24) := by
  have hb : ∀ k, 24 ≤ k → r.testBit k = false := fun k hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) hk))
  have h1 : ∀ y : Nat, y.testBit 0 = xs (fun k => y.testBit k) (List.range 1) := by
    intro y
    simp [xs]
  have e32 : (32 : Nat) = 24 + 8 := rfl
  have eland : Nat.land r v = r &&& v := rfl
  rw [parK_eq, and_one_beq, h1, xs_sx _ 1 2 rfl, xs_sx _ 2 4 rfl, xs_sx _ 4 8 rfl,
    xs_sx _ 8 16 rfl, xs_sx _ 16 32 rfl, e32,
    List.range_add, xs_append, xs_map, eland]
  rw [xs_congr (g := fun _ => false) (l := List.range 8), xs_false, Bool.xor_false]
  · exact xs_congr fun j _ => Nat.testBit_and ..
  · intro j _
    rw [Nat.testBit_and, hb _ (by omega), Bool.false_and]

theorem testBit_vecMulN_aux (v : Nat) (Y : Array Nat) (i : Nat) (L : List Nat) (acc : Nat) :
    (L.foldl (fun acc j => if v.testBit j then acc ^^^ (Y[j]?.getD 0) else acc) acc).testBit i =
      (acc.testBit i ^^ xs (fun j => v.testBit j && (Y[j]?.getD 0).testBit i) L) := by
  induction L generalizing acc with
  | nil => simp [xs_nil]
  | cons a L ih =>
    rw [List.foldl_cons, ih, xs_cons]
    by_cases h : v.testBit a = true <;> simp [h, Nat.testBit_xor]

theorem testBit_vecMulN (d : Nat) (Y : Array Nat) (v i : Nat) :
    (vecMulN d Y v).testBit i =
      xs (fun j => v.testBit j && (Y[j]?.getD 0).testBit i) (List.range d) := by
  rw [vecMulN, testBit_vecMulN_aux]
  simp

theorem testBit_ofBits_aux (f : Nat → Bool) (i : Nat) (L : List Nat) (acc : Nat) :
    (L.foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) acc).testBit i =
      (acc.testBit i || (decide (i ∈ L) && f i)) := by
  induction L generalizing acc with
  | nil => simp
  | cons a L ih =>
    rw [List.foldl_cons, ih]
    by_cases hi : a = i
    · subst hi
      by_cases h : f a = true <;> simp [h, Nat.testBit_or, Nat.one_shiftLeft]
    · by_cases h : f a = true <;>
        simp [h, hi, Ne.symm hi, Nat.testBit_or, Nat.one_shiftLeft]

theorem testBit_ofBits (d : Nat) (f : Nat → Bool) (i : Nat) :
    (ofBits d f).testBit i = (decide (i < d) && f i) := by
  rw [ofBits, testBit_ofBits_aux]
  simp

theorem testBit_foldr_or (f : Nat → Bool) (i : Nat) (L : List Nat) :
    (L.foldr (fun j s => if f j = true then Nat.lor s (Nat.shiftLeft 1 j) else s) 0).testBit i =
      (decide (i ∈ L) && f i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons]
    have e : ∀ x y : Nat, Nat.lor x (Nat.shiftLeft 1 y) = x ||| 1 <<< y := fun _ _ => rfl
    by_cases h : f a = true
    · rw [ite_eq_left h, e, Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hi : a = i
      · subst hi
        simp [h]
      · simp [hi, Ne.symm hi]
    · rw [ite_eq_right h, ih]
      by_cases hi : a = i
      · subst hi
        simp [h]
      · simp [Ne.symm hi]

theorem actK_eq_foldr (X v : Nat) : actK X v = (List.range 24).foldr (fun i s =>
    if Nat.beq (M24.parK (Nat.land (rowK X i) v)) 1 = true then Nat.lor s (Nat.shiftLeft 1 i)
    else s) 0 := by
  rw [actK, foldN_eq]
  simp only [nIf_eq]

theorem rowK_lt (X i : Nat) : rowK X i < 2 ^ 24 := by
  have e : rowK X i = (X >>> (24 * i)) &&& 16777215 := rfl
  rw [e]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem pg_rowK (P i : Nat) : pg 24 (mask 24) P i = rowK P i := rfl

theorem vecMulN_unpack (P v : Nat) :
    vecMulN 24 (transposeRows 24 (unpack 24 24 P)) v = actK P v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_vecMulN, actK_eq_foldr, testBit_foldr_or, parK_and _ _ (rowK_lt P i)]
  by_cases hi : i < 24
  · simp only [List.mem_range, hi, decide_true, Bool.true_and]
    apply xs_congr
    intro j hj
    rw [List.mem_range] at hj
    simp only [transposeRows, Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some,
      testBit_ofBits, unpack, pg_rowK, hi, decide_true, Bool.true_and, Bool.and_comm]
  · simp only [List.mem_range, hi, decide_false, Bool.false_and]
    rw [xs_congr (g := fun _ => false), xs_false]
    intro j hj
    rw [List.mem_range] at hj
    simp only [transposeRows, Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some,
      testBit_ofBits, hi, decide_false, Bool.false_and, Bool.and_false]

theorem ptK_lt (T : Nat → Nat) (k : Nat) : ptK T k < 2 ^ 24 := by
  have e : ptK T k = recK T k &&& 16777215 := rfl
  rw [e]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem ptK_lt' (T : Nat → Nat) (k : Nat) : ptK T k < 16777216 := ptK_lt T k

abbrev St := Std.HashSet Nat × Array (Nat × Nat × Nat)

def innerF (cols : Array Rows) (i v : Nat) (s : St) (g : Nat) : St :=
  if (!s.1.contains (vecMulN 24 (cols.getD g #[]) v)) = true then
    (s.1.insert (vecMulN 24 (cols.getD g #[]) v), s.2.push (vecMulN 24 (cols.getD g #[]) v, i, g))
  else (s.1, s.2)

def outerF (cols : Array Rows) (gens : List Nat) (s : St) (i : Nat) : St :=
  if h : i < s.2.size then gens.foldl (innerF cols i s.2[i].1) (s.1, s.2) else (s.1, s.2)

theorem ite_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem dite_yield {β : Type} (c : Prop) [Decidable c] (a : c → β) (b : ¬c → β) :
    (if h : c then (pure (ForInStep.yield (a h)) : Id (ForInStep β))
      else pure (ForInStep.yield (b h))) =
      pure (ForInStep.yield (if h : c then a h else b h)) := by
  split <;> rfl

theorem vBfs_eq (cols : Array Rows) (gens : List Nat) (root bound : Nat) :
    vBfs cols gens root bound = ((List.range bound).foldl (outerF cols gens)
      ((Std.HashSet.emptyWithCapacity 10000).insert root, #[(root, 0, 0)])).2 := by
  simp only [vBfs, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_yield,
    List.forIn_pure_yield_eq_foldl, pure_bind, dite_yield]
  have hsz : [:bound].size = bound := by simp [Std.Legacy.Range.size]
  rw [hsz, ← List.range_eq_range']
  rfl

theorem lvlGens_nil (M T E : Nat → Nat) (G h v p c : Nat) : lvlGens M T E G h v [] p c = c := rfl

theorem lvlGens_cons (M T E : Nat → Nat) (G h v g p c : Nat) (gs : List Nat) :
    lvlGens M T E G h v (g :: gs) p c =
      if c < failC then
        (if eK17 E (h * G + p) ≤ c ∧ ptK T (eK17 E (h * G + p)) = actK (M g) v then
          (if eK17 E (h * G + p) = c then
            (if VOrb.parK T (eK17 E (h * G + p)) = h ∧ genK T (eK17 E (h * G + p)) = g then
              lvlGens M T E G h v gs (p + 1) (c + 1) else failC)
          else lvlGens M T E G h v gs (p + 1) c)
        else failC)
      else failC := by
  change nIf(Nat.blt c failC,
      strictN (eK17 E (Nat.add (Nat.mul h G) p)) (fun e =>
      strictN (actK (M g) v) (fun w =>
        nIf(bAnd(Nat.ble e c, Nat.beq (ptK T e) w),
          nIf(Nat.beq e c,
            nIf(bAnd(Nat.beq (VOrb.parK T e) h, Nat.beq (genK T e) g),
              lvlGens M T E G h v gs (Nat.succ p) (Nat.succ c), failC),
            lvlGens M T E G h v gs (Nat.succ p) c),
          failC))), failC) = _
  simp only [strictN_eq, nIf_eq, bAnd_eq, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, Bool.and_eq_true,
    Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one]

theorem lvlGens_cons_ok {M T E : Nat → Nat} {G h v g p c r : Nat} {gs : List Nat}
    (H : lvlGens M T E G h v (g :: gs) p c = r) (hr : r < failC) :
    c < failC ∧ ∃ e, e ≤ c ∧ ptK T e = actK (M g) v ∧
      ((e = c ∧ VOrb.parK T c = h ∧ genK T c = g ∧ lvlGens M T E G h v gs (p + 1) (c + 1) = r) ∨
        (e < c ∧ lvlGens M T E G h v gs (p + 1) c = r)) := by
  rw [lvlGens_cons] at H
  by_cases h1 : c < failC
  · rw [ite_eq_left h1] at H
    refine ⟨h1, eK17 E (h * G + p), ?_⟩
    by_cases h2 : eK17 E (h * G + p) ≤ c ∧ ptK T (eK17 E (h * G + p)) = actK (M g) v
    · rw [ite_eq_left h2] at H
      refine ⟨h2.1, h2.2, ?_⟩
      by_cases h3 : eK17 E (h * G + p) = c
      · rw [ite_eq_left h3] at H
        by_cases h4 : VOrb.parK T (eK17 E (h * G + p)) = h ∧ genK T (eK17 E (h * G + p)) = g
        · rw [ite_eq_left h4] at H
          rw [h3] at h4
          exact Or.inl ⟨h3, h4.1, h4.2, H⟩
        · rw [ite_eq_right h4] at H
          omega
      · rw [ite_eq_right h3] at H
        exact Or.inr ⟨by omega, H⟩
    · rw [ite_eq_right h2] at H
      omega
  · rw [ite_eq_right h1] at H
    omega

theorem lvlGens_mono {M T E : Nat → Nat} {G h v : Nat} :
    ∀ (gs : List Nat) (p c r : Nat), lvlGens M T E G h v gs p c = r → r < failC → c ≤ r
  | [], p, c, r, H, _ => by
    rw [lvlGens_nil] at H
    omega
  | g :: gs, p, c, r, H, hr => by
    obtain ⟨_, e, _, _, h | h⟩ := lvlGens_cons_ok H hr
    · have := lvlGens_mono gs _ _ _ h.2.2.2 hr
      omega
    · have := lvlGens_mono gs _ _ _ h.2 hr
      omega

noncomputable def gstepR (M : Nat → Nat) (gens : List Nat) (n : Nat) (T E : Nat → Nat)
    (G h c : Nat) : Nat :=
  nIf(Nat.blt c failC, nIf(Nat.blt h n, nIf(Nat.blt h c,
    strictN (ptK T h) (fun v => lvlGens M T E G h v gens (nat_lit 0) c), failC), c), failC)

theorem levelSl_iff (M : Nat → Nat) (gens : List Nat) (n : Nat) (T E : Nat → Nat)
    (lo len c₀ c₁ : Nat) : levelSl M gens n T E lo len c₀ c₁ = true ↔
      (List.range len).foldl (fun c d => gstepR M gens n T E (lenN gens) (lo + d) c) c₀ = c₁ := by
  have e : levelSl M gens n T E lo len c₀ c₁ = Nat.beq (foldUp len (fun d c =>
      strictN (Nat.add lo d) (fun h => gstepR M gens n T E (lenN gens) h c)) c₀) c₁ := by
    rw [levelSl, strictB_eq]
    rfl
  rw [e, Nat.beq_eq, foldUp_eq]
  simp only [strictN_eq, Nat.add_eq]

section Level

variable {M : Nat → Nat} {gens : List Nat} {n : Nat} {T E : Nat → Nat} {G : Nat}

theorem gstepR_eq (h c : Nat) : gstepR M gens n T E G h c =
    if c < failC then (if h < n then (if h < c then lvlGens M T E G h (ptK T h) gens 0 c
      else failC) else c) else failC := by
  simp only [gstepR, nIf_eq, Nat.blt_eq, strictN_eq]

theorem gstepR_ok {h c : Nat} (hr : gstepR M gens n T E G h c < failC) : c < failC ∧
    ((h < n ∧ h < c ∧ lvlGens M T E G h (ptK T h) gens 0 c = gstepR M gens n T E G h c) ∨
      (n ≤ h ∧ gstepR M gens n T E G h c = c)) := by
  have e := gstepR_eq (M := M) (gens := gens) (n := n) (T := T) (E := E) (G := G) h c
  by_cases h1 : c < failC
  · rw [ite_eq_left h1] at e
    refine ⟨h1, ?_⟩
    by_cases h2 : h < n
    · rw [ite_eq_left h2] at e
      by_cases h3 : h < c
      · rw [ite_eq_left h3] at e
        exact Or.inl ⟨h2, h3, e.symm⟩
      · rw [ite_eq_right h3] at e
        omega
    · rw [ite_eq_right h2] at e
      exact Or.inr ⟨by omega, e⟩
  · rw [ite_eq_right h1] at e
    omega

theorem gstepR_mono {h c : Nat} (hr : gstepR M gens n T E G h c < failC) :
    c ≤ gstepR M gens n T E G h c ∧ c < failC := by
  obtain ⟨h1, ⟨-, -, h2⟩ | ⟨-, h2⟩⟩ := gstepR_ok hr
  · exact ⟨lvlGens_mono gens 0 c _ h2 hr, h1⟩
  · omega

theorem fold_mono : ∀ (L : List Nat) (c : Nat),
    L.foldl (fun c h => gstepR M gens n T E G h c) c < failC →
      c ≤ L.foldl (fun c h => gstepR M gens n T E G h c) c ∧ c < failC
  | [], c, hr => by
    simp only [List.foldl_nil] at hr ⊢
    omega
  | h :: L, c, hr => by
    simp only [List.foldl_cons] at hr ⊢
    have h1 := fold_mono L _ hr
    have h2 := gstepR_mono h1.2
    omega

theorem fold_tail : ∀ (L : List Nat), (∀ h ∈ L, n ≤ h) → ∀ c : Nat,
    L.foldl (fun c h => gstepR M gens n T E G h c) c < failC →
      L.foldl (fun c h => gstepR M gens n T E G h c) c = c
  | [], _, c, _ => rfl
  | h :: L, hL, c, hr => by
    simp only [List.foldl_cons] at hr ⊢
    have h1 := fold_tail L (fun x hx => hL x (List.mem_cons_of_mem _ hx)) _ hr
    rw [h1] at hr ⊢
    obtain ⟨-, ⟨hh, -⟩ | ⟨-, he⟩⟩ := gstepR_ok hr
    · have := hL h (List.mem_cons_self ..)
      omega
    · exact he

theorem fold_slices {C : Nat → Nat} {L NS : Nat}
    (hsl : ∀ s < NS, (List.range L).foldl (fun c d => gstepR M gens n T E G (s * L + d) c) (C s) =
      C (s + 1)) :
    ∀ s ≤ NS, (List.range (s * L)).foldl (fun c h => gstepR M gens n T E G h c) (C 0) = C s
  | 0, _ => by simp
  | s + 1, hs => by
    rw [Nat.succ_mul, List.range_add, List.foldl_append, fold_slices hsl s (by omega),
      List.foldl_map]
    exact hsl s (by omega)

noncomputable def entT (T : Nat → Nat) (k : Nat) : Nat × Nat × Nat :=
  (ptK T k, if k = 0 then 0 else VOrb.parK T k, if k = 0 then 0 else genK T k)

structure Rel (M : Nat → Nat) (gens : List Nat) (T : Nat → Nat) (c : Nat) (s : St) : Prop where
  size : s.2.size = c
  ent : ∀ k < c, s.2[k]? = some (entT T k)
  tree : ∀ k < c, 0 < k → VOrb.parK T k < k ∧ genK T k ∈ gens ∧
    ptK T k = actK (M (genK T k)) (ptK T (VOrb.parK T k))
  seen : ∀ w, s.1.contains w = true ↔ ∃ k < c, ptK T k = w

theorem Rel.get {c : Nat} {s : St} (hs : Rel M gens T c s) {k : Nat} (hk : k < c) :
    s.2[k]'(hs.size ▸ hk) = entT T k := by
  have := hs.ent k hk
  rw [Array.getElem?_eq_getElem (hs.size ▸ hk)] at this
  exact Option.some.inj this

theorem rel_init {root : Nat} (hroot : ptK T 0 = root) :
    Rel M gens T 1 ((Std.HashSet.emptyWithCapacity 10000).insert root, #[(root, 0, 0)]) where
  size := rfl
  ent k hk := by
    have : k = 0 := by omega
    subst this
    simp [entT, hroot]
  tree k hk h0 := by omega
  seen w := by
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_emptyWithCapacity, Bool.or_false,
      beq_iff_eq]
    constructor
    · intro h
      exact ⟨0, by omega, hroot.trans h⟩
    · rintro ⟨k, hk, hk'⟩
      have : k = 0 := by omega
      subst this
      exact hroot.symm.trans hk'

theorem rel_push {c h g : Nat} {s : St} (hs : Rel M gens T c s) (hhc : h < c)
    (hpar : VOrb.parK T c = h) (hgen : genK T c = g) (hg : g ∈ gens)
    (hpt : ptK T c = actK (M g) (ptK T h)) :
    Rel M gens T (c + 1) (s.1.insert (ptK T c), s.2.push (ptK T c, h, g)) where
  size := by simp [hs.size]
  ent k hk := by
    simp only [Array.getElem?_push, hs.size]
    by_cases hkc : k = c
    · subst hkc
      have hk0 : k ≠ 0 := by omega
      simp [entT, hpar, hgen, hk0]
    · rw [ite_eq_right hkc]
      exact hs.ent k (by omega)
  tree k hk h0 := by
    by_cases hkc : k = c
    · subst hkc
      rw [hpar, hgen]
      exact ⟨hhc, hg, hpt⟩
    · exact hs.tree k (by omega) h0
  seen w := by
    rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hs.seen]
    constructor
    · rintro (h | ⟨k, hk, hk'⟩)
      · exact ⟨c, by omega, h⟩
      · exact ⟨k, by omega, hk'⟩
    · rintro ⟨k, hk, hk'⟩
      by_cases hkc : k = c
      · subst hkc
        exact Or.inl hk'
      · exact Or.inr ⟨k, by omega, hk'⟩

theorem inner_sim {cols : Array Rows}
    (hcols : ∀ g ∈ gens, ∀ v, vecMulN 24 (cols.getD g #[]) v = actK (M g) v)
    (hdist : ∀ a < n, ∀ b < n, ptK T a = ptK T b → a = b) {h v : Nat} (hv : v = ptK T h)
    (gs : List Nat) (hgs : ∀ g ∈ gs, g ∈ gens) :
    ∀ (p c : Nat) (s : St), Rel M gens T c s → h < c → lvlGens M T E G h v gs p c < failC →
      lvlGens M T E G h v gs p c ≤ n →
        Rel M gens T (lvlGens M T E G h v gs p c) (gs.foldl (innerF cols h v) s) := by
  induction gs with
  | nil =>
    intro p c s hs _ _ _
    exact hs
  | cons g gs ih =>
    intro p c s hs hhc hr hrn
    have hg : g ∈ gens := hgs g (List.mem_cons_self ..)
    have ih' := ih fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    obtain ⟨-, e, he, hpe, ⟨hec, hpar, hgen, H'⟩ | ⟨hec, H'⟩⟩ := lvlGens_cons_ok rfl hr
    · subst hec
      rw [← H'] at hr hrn ⊢
      have hcr := lvlGens_mono gs _ _ _ rfl hr
      have hw : vecMulN 24 (cols.getD g #[]) v = ptK T e := by rw [hcols g hg, hpe]
      have hnot : s.1.contains (ptK T e) = false := by
        rcases hcs : s.1.contains (ptK T e) with _ | _
        · rfl
        · obtain ⟨k, hk, hk'⟩ := (hs.seen _).1 hcs
          have := hdist k (by omega) e (by omega) hk'
          omega
      rw [List.foldl_cons]
      have hstep : innerF cols h v s g = (s.1.insert (ptK T e), s.2.push (ptK T e, h, g)) := by
        simp only [innerF, hw, hnot, Bool.not_false, ↓reduceIte]
      rw [hstep]
      refine ih' (p + 1) (e + 1) _ ?_ (by omega) hr hrn
      exact rel_push hs hhc hpar hgen hg (by rw [hpe, hv])
    · rw [← H'] at hr hrn ⊢
      have hw : vecMulN 24 (cols.getD g #[]) v = ptK T e := by rw [hcols g hg, hpe]
      have hyes : s.1.contains (ptK T e) = true := (hs.seen _).2 ⟨e, hec, rfl⟩
      rw [List.foldl_cons]
      have hstep : innerF cols h v s g = (s.1, s.2) := by
        simp only [innerF, hw, hyes, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hstep]
      exact ih' (p + 1) c _ hs hhc hr hrn

theorem outer_sim {cols : Array Rows} {root : Nat}
    (hcols : ∀ g ∈ gens, ∀ v, vecMulN 24 (cols.getD g #[]) v = actK (M g) v)
    (hdist : ∀ a < n, ∀ b < n, ptK T a = ptK T b → a = b) (hroot : ptK T 0 = root)
    (hn : n < failC)
    (hcnt : (List.range n).foldl (fun c h => gstepR M gens n T E G h c) 1 = n) :
    ∀ i ≤ n, Rel M gens T ((List.range i).foldl (fun c h => gstepR M gens n T E G h c) 1)
      ((List.range i).foldl (outerF cols gens)
        ((Std.HashSet.emptyWithCapacity 10000).insert root, #[(root, 0, 0)]))
  | 0, _ => rel_init hroot
  | i + 1, hi => by
    have ih := outer_sim hcols hdist hroot hn hcnt i (by omega)
    have hsplit : (List.range n).foldl (fun c h => gstepR M gens n T E G h c) 1 =
        ((List.range (n - (i + 1))).map (i + 1 + ·)).foldl (fun c h => gstepR M gens n T E G h c)
          ((List.range (i + 1)).foldl (fun c h => gstepR M gens n T E G h c) 1) := by
      rw [← List.foldl_append, ← List.range_add, Nat.add_sub_cancel' hi]
    have hlt : ((List.range (n - (i + 1))).map (i + 1 + ·)).foldl
        (fun c h => gstepR M gens n T E G h c)
          ((List.range (i + 1)).foldl (fun c h => gstepR M gens n T E G h c) 1) < failC := by
      rw [← hsplit, hcnt]
      exact hn
    have hle := fold_mono _ _ hlt
    rw [← hsplit, hcnt] at hle
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hle ⊢
    generalize (List.range i).foldl (fun c h => gstepR M gens n T E G h c) 1 = C at ih hle ⊢
    generalize (List.range i).foldl (outerF cols gens)
      ((Std.HashSet.emptyWithCapacity 10000).insert root, #[(root, 0, 0)]) = s at ih ⊢
    obtain ⟨-, ⟨-, hic, hlv⟩ | ⟨hni, -⟩⟩ := gstepR_ok hle.2
    · have hsz : i < s.2.size := by
        rw [ih.size]
        exact hic
      have hv : s.2[i].1 = ptK T i := by
        rw [ih.get hic]
        rfl
      simp only [outerF, hsz, ↓reduceDIte, hv]
      rw [← hlv] at hle ⊢
      exact inner_sim hcols hdist rfl gens (fun g hg => hg) 0 C s ih hic hle.2 hle.1
    · omega

end Level

theorem perm_pos {S T : Nat → Nat} {n NS L : Nat} (hNL : n ≤ NS * L)
    (hps : ∀ s < NS, permSl S T n (s * L) L = true) : ∀ k < n,
      msK S k < n ∧ invK S k < n ∧ invK S (msK S k) = k ∧ msK S (invK S k) = k ∧
        (k + 1 < n → ptK T (msK S k) < ptK T (msK S (k + 1))) := by
  intro k hk
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Nat.mul_zero] at hNL
      omega
    · exact h
  have hs : k / L < NS := (Nat.div_lt_iff_lt_mul hL).2 (by omega)
  have H0 := hps (k / L) hs
  rw [permSl, allN_iff] at H0
  have H := H0 (k % L) (Nat.mod_lt k hL)
  have e : Nat.add (k / L * L) (k % L) = k := Nat.div_add_mod' k L
  simp only [strictB_eq, e] at H
  simp only [bAnd_eq] at H
  simp only [bIf_eq] at H
  simp only [Nat.blt_eq, Nat.beq_eq, hk, ↓reduceIte, Bool.and_eq_true, Nat.succ_eq_add_one] at H
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨h1, h2, h3, h4, fun hk1 => ?_⟩
  simpa [hk1] using h5

theorem perm_dist {S T : Nat → Nat} {n : Nat}
    (hP : ∀ k < n, msK S k < n ∧ invK S k < n ∧ invK S (msK S k) = k ∧ msK S (invK S k) = k ∧
      (k + 1 < n → ptK T (msK S k) < ptK T (msK S (k + 1)))) :
    ∀ a < n, ∀ b < n, ptK T a = ptK T b → a = b := by
  have hinc : ∀ j, j < n → ∀ i, i < j → ptK T (msK S i) < ptK T (msK S j) := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hij
      have h5 := (hP j (by omega)).2.2.2.2 hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with h | h
      · exact Nat.lt_trans (ih (by omega) i h) h5
      · subst h
        exact h5
  intro a ha b hb hab
  obtain ⟨-, hra, -, hma, -⟩ := hP a ha
  obtain ⟨-, hrb, -, hmb, -⟩ := hP b hb
  rcases Nat.lt_trichotomy (invK S a) (invK S b) with h | h | h
  · have := hinc _ hrb _ h
    rw [hma, hmb] at this
    omega
  · rw [← hma, ← hmb, h]
  · have := hinc _ hra _ h
    rw [hma, hmb] at this
    omega

theorem vSorted_of : ∀ l : List Nat, l.Pairwise (· < ·) → vSorted l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: r, h => by
    rw [vSorted]
    rw [List.pairwise_cons] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.1 b (List.mem_cons_self ..), vSorted_of (b :: r) h.2⟩

theorem mergeSort_lt {l : List Nat} (hl : l.Nodup) :
    (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· < ·) := by
  have h1 := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have h2 : (l.mergeSort fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm l _).nodup_iff.2 hl
  exact (h1.and h2).imp fun ⟨h3, h4⟩ => Nat.lt_of_le_of_ne (by simpa using h3) h4

theorem vtree_of_rel {M : Nat → Nat} {gens : List Nat} {n : Nat} {T : Nat → Nat}
    {cols : Array Rows} {root : Nat} {s : St}
    (hcols : ∀ g ∈ gens, ∀ v, vecMulN 24 (cols.getD g #[]) v = actK (M g) v)
    (hdist : ∀ a < n, ∀ b < n, ptK T a = ptK T b → a = b) (hroot : ptK T 0 = root) (hn0 : 0 < n)
    (hs : Rel M gens T n s) : vTreeOK cols gens root n s.2 = true := by
  have hget : ∀ k < n, s.2.getD k (0, 0, 0) = entT T k := fun k hk => by
    rw [Array.getD_eq_getD_getElem?, hs.ent k hk]
    rfl
  have hmap : s.2.toList.map (·.1) = (List.range n).map (ptK T) := by
    apply List.ext_getElem
    · simp [hs.size]
    · intro k h1 h2
      have hk : k < n := by simpa using h2
      simp only [List.getElem_map, Array.getElem_toList, List.getElem_range]
      rw [hs.get hk]
      rfl
  have hnd : ((List.range n).map (ptK T)).Nodup :=
    List.pairwise_map.2 (List.nodup_range.imp_of_mem fun ha hb hab heq =>
      hab (hdist _ (List.mem_range.1 ha) _ (List.mem_range.1 hb) heq))
  simp only [vTreeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hs.size, ?_⟩, ?_⟩, ?_⟩
  · rw [hget 0 hn0]
    exact hroot
  · intro m hm
    rw [hget m hm]
    by_cases hm0 : m = 0
    · subst hm0
      simp [entT, ptK_lt']
    · obtain ⟨hp, hg, hpt⟩ := hs.tree m hm (by omega)
      simp only [entT, hm0, ↓reduceIte]
      rw [hget _ (by omega)]
      simp [entT, ptK_lt', hp, hg, hcols _ hg, ← hpt, -Array.getD_eq_getD_getElem?]
  · rw [hmap]
    exact vSorted_of _ (mergeSort_lt hnd)

theorem level_ok {M : Nat → Nat} {gens : List Nat} {cols : Array Rows} {root n : Nat}
    {T E S C : Nat → Nat} {NS L : Nat}
    (hcols : ∀ g ∈ gens, ∀ v, vecMulN 24 (cols.getD g #[]) v = actK (M g) v)
    (hn0 : 0 < n) (hn : n < 131072) (hroot : ptK T 0 = root) (hC0 : C 0 = 1) (hCN : C NS = n)
    (hNL : n ≤ NS * L)
    (hsl : ∀ s < NS, levelSl M gens n T E (s * L) L (C s) (C (s + 1)) = true)
    (hps : ∀ s < NS, permSl S T n (s * L) L = true) :
    vTreeOK cols gens root n (vBfs cols gens root n) = true := by
  have hdist := perm_dist (perm_pos hNL hps)
  have hfail : n < failC := by
    change n < 1048576
    omega
  have hsl' := fun s hs => (levelSl_iff M gens n T E (s * L) L (C s) (C (s + 1))).1 (hsl s hs)
  have hall := fold_slices hsl' NS (Nat.le_refl _)
  have eNL : NS * L = n + (NS * L - n) := by omega
  rw [hC0, hCN, eNL, List.range_add, List.foldl_append] at hall
  have hcnt : (List.range n).foldl (fun c h => gstepR M gens n T E (lenN gens) h c) 1 = n := by
    have ht := fold_tail (M := M) (gens := gens) (n := n) (T := T) (E := E) (G := lenN gens)
      ((List.range (NS * L - n)).map (n + ·)) (by simp) _ (by rw [hall]; exact hfail)
    rw [← ht]
    exact hall
  have hrel := outer_sim (cols := cols) hcols hdist hroot hfail hcnt n (Nat.le_refl _)
  rw [hcnt] at hrel
  rw [vBfs_eq]
  exact vtree_of_rel hcols hdist hroot hn0 hrel

public theorem tower_ok {M : Nat → Nat} {K : Nat} {base sizes : List Nat} {gens : List (List Nat)}
    (hn : ∀ i < base.length, 0 < sizes.getD i 0 ∧ sizes.getD i 0 < 131072)
    (hl : ∀ i < base.length, ∃ (T E S C : Nat → Nat) (NS L : Nat),
      levelHd K (gens.getD i []) (base.getD i 0) T = true ∧ C 0 = 1 ∧
        C NS = sizes.getD i 0 ∧ sizes.getD i 0 ≤ NS * L ∧
        (∀ s < NS, levelSl M (gens.getD i []) (sizes.getD i 0) T E (s * L) L (C s) (C (s + 1)) =
          true) ∧
        (∀ s < NS, permSl S T (sizes.getD i 0) (s * L) L = true) ∧
        fixesK M (gens.getD i []) base i = true) :
    vTowerOK (Array.ofFn (n := K) fun j => transposeRows 24 (unpack 24 24 (M j.val))) base gens
      sizes = true := by
  have hcols : ∀ g < K, ∀ v, vecMulN 24 ((Array.ofFn (n := K) fun j =>
      transposeRows 24 (unpack 24 24 (M j.val))).getD g #[]) v = actK (M g) v := by
    intro g hg v
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hg, ↓reduceDIte, Option.getD_some]
    exact vecMulN_unpack (M g) v
  simp only [vTowerOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Array.size_ofFn, beq_iff_eq]
  intro i hi
  obtain ⟨T, E, S, C, NS, L, hhd, hC0, hCN, hNL, hsl, hps, hfix⟩ := hl i hi
  have hhd' : (∀ x ∈ gens.getD i [], x < K) ∧ ptK T 0 = base.getD i 0 := by
    have e : levelHd K (gens.getD i []) (base.getD i 0) T =
        (allLtN K (gens.getD i []) && Nat.beq (ptK T 0) (base.getD i 0)) := bAnd_eq _ _
    rw [e, Bool.and_eq_true, allLtN_iff, Nat.beq_eq] at hhd
    exact hhd
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← hhd'.2]
    exact ptK_lt T 0
  · intro j hj
    refine ⟨hhd'.1 j hj, fun l hl => ?_⟩
    rw [hcols j (hhd'.1 j hj)]
    exact (fixesK_iff _ _ _ _).1 hfix j hj l hl
  · exact level_ok (fun g hg => hcols g (hhd'.1 g hg)) (hn i hi).1 (hn i hi).2 hhd'.2 hC0 hCN hNL
      hsl hps

end CFSG.KS.SporSch.VOrb.TowerLib
