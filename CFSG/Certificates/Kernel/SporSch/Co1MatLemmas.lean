module

public import Certificates.Data.Kernel.SporSch.Co1Mat
public import Certificates.Data.CFSGNative.Co1Schreier.Base
public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch.M24.MatL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = (if c = true then t else e) := by
  cases c <;> rfl

theorem foldBlk_succ (b : Nat) (f : Nat → Nat → Nat) (l s : Nat) :
    foldBlk b f (l + 1) s = foldBlk b f l (f (b + l) s) :=
  strictN_eq (f (b + l) s) (foldBlk b f l)

theorem foldBlk_eq (b : Nat) (f : Nat → Nat → Nat) (len s : Nat) :
    foldBlk b f len s = (List.range len).foldr (fun l s => f (b + l) s) s := by
  induction len generalizing s with
  | zero => rfl
  | succ len ih =>
    rw [foldBlk_succ, ih, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]

theorem foldN_eq (f : Nat → Nat → Nat) (s : Nat) :
    foldN 24 f s = (List.range 24).foldr f s := by
  have h : foldN 24 f s = foldBlk 0 f 24 s := rfl
  rw [h, foldBlk_eq]
  simp only [Nat.zero_add]

theorem allBlk_eq (b : Nat) (f : Nat → Bool) (len : Nat) :
    allBlk b f len = (List.range len).all fun l => f (b + l) := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have hs : allBlk b f (len + 1) = (f (b + len) && allBlk b f len) := rfl
    rw [hs, List.range_succ, List.all_append, ← ih, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_comm]

theorem shiftLeft_six (x : Nat) : Nat.shiftLeft x (nat_lit 6) = x * 64 := by
  change x <<< 6 = x * 64
  rw [Nat.shiftLeft_eq]

theorem all_range_add (f : Nat → Bool) (a b : Nat) :
    (List.range (a + b)).all f
      = ((List.range a).all f && (List.range b).all fun l => f (a + l)) := by
  simp only [List.range_add, List.all_append, List.all_map, Function.comp_def]

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
    rw [hs, ih, allBlk_eq, shiftLeft_six h, show (h + 1) * 64 = h * 64 + 64 by omega,
      all_range_add f (h * 64) 64, Bool.and_comm]

theorem allN_eq (n : Nat) (f : Nat → Bool) : allN n f = (List.range n).all f := by
  have hs : allN n f = (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) &&
        Nat.rec (motive := fun _ => Bool) true
          (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
            (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64)))
          (Nat.shiftRight n (nat_lit 6))) :=
    rfl
  have e1 : Nat.shiftRight n (nat_lit 6) = n / 64 := Nat.shiftRight_eq_div_pow n 6
  have e2 : Nat.land n (nat_lit 63) = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
  rw [hs, allN_rec_eq, allBlk_eq, shiftLeft_six, e2, e1, Bool.and_comm,
    ← all_range_add f (n / 64 * 64) (n % 64), show n / 64 * 64 + n % 64 = n by omega]

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  rw [allN_eq, List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.2 hi), fun h x hx => h x (List.mem_range.1 hx)⟩

theorem hasBit_eq (M l : Nat) : hasBit M l = M.testBit l := by
  have e1 : Nat.shiftLeft 1 l = 2 ^ l := Nat.one_shiftLeft l
  change Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 l)) = M.testBit l
  rw [e1]
  cases hM : M.testBit l with
  | false =>
    have h0 : Nat.land M (2 ^ l) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      change (M &&& 2 ^ l).testBit i = (0 : Nat).testBit i
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hli : l = i
      · subst hli
        simp [hM]
      · simp [hli]
    rw [h0]
    rfl
  | true =>
    have h1 : Nat.land M (2 ^ l) = 2 ^ l := by
      apply Nat.eq_of_testBit_eq
      intro i
      change (M &&& 2 ^ l).testBit i = (2 ^ l).testBit i
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hli : l = i
      · subst hli
        simp [hM]
      · simp [hli]
    rw [h1, Nat.blt_eq]
    exact Nat.two_pow_pos l

@[expose] def rowV (X i : Nat) : Nat := X / 2 ^ (24 * i) % 2 ^ 24

theorem rowV_lt (X i : Nat) : rowV X i < 2 ^ 24 := Nat.mod_lt _ (Nat.two_pow_pos 24)

theorem rowK_eq (X i : Nat) : rowK X i = rowV X i := by
  have h : (16777215 : Nat) = 2 ^ 24 - 1 := by norm_num
  change (X >>> (24 * i)) &&& 16777215 = _
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, rowV]

theorem unpack_size (X : Nat) : (unpack 24 24 X).size = 24 := by
  simp [unpack]

theorem unpack_getElem (X i : Nat) (hi : i < (unpack 24 24 X).size) :
    (unpack 24 24 X)[i] = rowV X i := by
  have h : (16777215 : Nat) = 2 ^ 24 - 1 := by norm_num
  simp only [unpack, Array.getElem_ofFn]
  change (X >>> (24 * i)) &&& ((1 <<< 24) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, rowV]

theorem unpack_getD (X i : Nat) (hi : i < 24) : (unpack 24 24 X)[i]?.getD 0 = rowV X i := by
  have hs : i < (unpack 24 24 X).size := by rw [unpack_size]; exact hi
  rw [Array.getElem?_eq_getElem hs, Option.getD_some, unpack_getElem]

theorem foldl_xor_acc (p : Nat → Bool) (g : Nat → Nat) (l : List Nat) (a : Nat) :
    l.foldl (fun acc j => if p j = true then acc ^^^ g j else acc) a =
      a ^^^ l.foldl (fun acc j => if p j = true then acc ^^^ g j else acc) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (if p x = true then 0 ^^^ g x else 0)]
    split <;> simp [Nat.xor_assoc]

theorem foldr_xor_eq_foldl (p : Nat → Bool) (g : Nat → Nat) (l : List Nat) :
    l.foldr (fun j s => if p j = true then s ^^^ g j else s) 0 =
      l.foldl (fun acc j => if p j = true then acc ^^^ g j else acc) 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.foldl_cons]
    by_cases hx : p x = true
    · simp only [hx, ite_true, Nat.zero_xor]
      rw [foldl_xor_acc p g l (g x), Nat.xor_comm]
    · simp [hx]

theorem foldl_xor_lt (p : Nat → Bool) (g : Nat → Nat) (l : List Nat) (a : Nat)
    (ha : a < 2 ^ 24) (hg : ∀ j, g j < 2 ^ 24) :
    l.foldl (fun acc j => if p j = true then acc ^^^ g j else acc) a < 2 ^ 24 := by
  induction l generalizing a with
  | nil => exact ha
  | cons x l ih =>
    rw [List.foldl_cons]
    apply ih
    split
    · exact Nat.xor_lt_two_pow ha (hg x)
    · exact ha

theorem pack_testBit (f : Nat → Nat) (l : List Nat) (t : Nat) :
    (l.foldr (fun i s => Nat.lor s (Nat.shiftLeft (f i) (Nat.mul 24 i))) 0).testBit t =
      l.any (fun i => decide (24 * i ≤ t) && (f i).testBit (t - 24 * i)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.foldr_cons, List.any_cons]
    change ((l.foldr (fun i s => Nat.lor s (Nat.shiftLeft (f i) (Nat.mul 24 i))) 0) |||
      (f x <<< (24 * x))).testBit t = _
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft, Bool.or_comm]

theorem testBit_false_of_lt {x b : Nat} (hx : x < 2 ^ 24) (hb : 24 ≤ b) : x.testBit b = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hb))

theorem pack_field (f : Nat → Nat) (hf : ∀ i < 24, f i < 2 ^ 24) (k : Nat) (hk : k < 24) :
    rowV ((List.range 24).foldr (fun i s => Nat.lor s (Nat.shiftLeft (f i) (Nat.mul 24 i))) 0) k =
      f k := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [rowV, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, pack_testBit]
  by_cases hb : b < 24
  · rw [decide_eq_true hb, Bool.true_and]
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true]
    constructor
    · rintro ⟨i, hi, h⟩
      rw [Bool.and_eq_true, decide_eq_true_iff] at h
      have hi24 := List.mem_range.1 hi
      have hik : i = k := by
        rcases Nat.lt_trichotomy i k with h1 | h1 | h1
        · exfalso
          have := testBit_false_of_lt (hf i hi24) (by omega : 24 ≤ b + 24 * k - 24 * i)
          rw [this] at h
          exact Bool.false_ne_true h.2
        · exact h1
        · omega
      subst hik
      have e : b + 24 * i - 24 * i = b := by omega
      rw [← e]
      exact h.2
    · intro h
      refine ⟨k, List.mem_range.2 hk, ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_iff]
      have e : b + 24 * k - 24 * k = b := by omega
      exact ⟨by omega, by rw [e]; exact h⟩
  · rw [decide_eq_false hb, Bool.false_and, testBit_false_of_lt (hf k hk) (by omega)]

theorem unpack_pack (f : Nat → Nat) (hf : ∀ i < 24, f i < 2 ^ 24) :
    unpack 24 24 (foldN 24 (fun i s => Nat.lor s (Nat.shiftLeft (f i) (Nat.mul 24 i))) 0) =
      Array.ofFn (n := 24) fun i => f i.val := by
  apply Array.ext
  · rw [unpack_size, Array.size_ofFn]
  · intro i h1 h2
    rw [unpack_getElem, Array.getElem_ofFn, foldN_eq]
    exact pack_field f hf i (by rw [unpack_size] at h1; exact h1)

theorem vmulK_eq (v Y : Nat) : vmulK v Y = vecMulN 24 (unpack 24 24 Y) v := by
  unfold vmulK vecMulN
  rw [foldN_eq]
  simp only [nIf_eq, hasBit_eq, rowK_eq]
  change (List.range 24).foldr (fun j s => if v.testBit j = true then s ^^^ rowV Y j else s) 0 = _
  rw [foldr_xor_eq_foldl]
  apply List.foldl_ext
  intro a j hj
  rw [unpack_getD Y j (List.mem_range.1 hj)]

theorem vmulK_lt (v Y : Nat) : vmulK v Y < 2 ^ 24 := by
  unfold vmulK
  rw [foldN_eq]
  simp only [nIf_eq, hasBit_eq, rowK_eq]
  change (List.range 24).foldr (fun j s => if v.testBit j = true then s ^^^ rowV Y j else s) 0 < _
  rw [foldr_xor_eq_foldl]
  exact foldl_xor_lt _ _ _ 0 (Nat.two_pow_pos 24) (rowV_lt Y)

theorem unpack_mulK (X Y : Nat) :
    unpack 24 24 (mulK X Y) = mul (unpack 24 24 X) (unpack 24 24 Y) := by
  unfold mulK
  rw [unpack_pack (fun i => vmulK (rowK X i) Y) (fun i _ => vmulK_lt _ _)]
  apply Array.ext
  · simp [mul, mulRows, unpack_size]
  · intro i h1 h2
    simp only [mul, mulRows, Array.getElem_map, Array.getElem_ofFn]
    rw [unpack_getElem, vmulK_eq, rowK_eq]

theorem unpack_idM : unpack 24 24 idM = one () := by
  unfold idM
  rw [unpack_pack (fun i => Nat.shiftLeft 1 i) ?_]
  · rfl
  · intro i hi
    change 1 <<< i < 2 ^ 24
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by norm_num) hi

@[expose] def pivStep (M : Array Nat) (c p r : Nat) : Nat :=
  if (p == 24 && (M[r]!).testBit c) = true then r else p

@[expose] def pivF (M : Array Nat) (c : Nat) : Nat :=
  (List.range' c (24 - c)).foldl (pivStep M c) 24

@[expose] def elimStep (c rp : Nat) (M : Array Nat) (r : Nat) : Array Nat :=
  if (r != c && (M[r]!).testBit c) = true then M.set! r (M[r]! ^^^ rp) else M

@[expose] def elimF (M : Array Nat) (c rp : Nat) : Array Nat :=
  (List.range 24).foldl (elimStep c rp) M

@[expose] def stepF (M : Array Nat) (c : Nat) : Array Nat :=
  if pivF M c < 24 then
    elimF ((M.set! (pivF M c) M[c]!).set! c M[pivF M c]!) c M[pivF M c]!
  else M

@[expose] def initF (X : Rows) : Array Nat := Array.ofFn (n := 24) fun i =>
  ((X[i.val]?.getD 0) % 2 ^ 24) ||| (1 <<< (24 + i.val))

@[expose] def invF (X : Rows) : Rows := ((List.range 24).foldl stepF (initF X)).map (· >>> 24)

theorem ite_pure_yield {β : Type} (p : Prop) [Decidable p] (a b : β) :
    (if p then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if p then a else b)) := by
  split <;> rfl

theorem inv_eq_invF (X : Rows) : CFSG.Sporadic.Co1Schreier.Native.inv X = invF X := by
  unfold CFSG.Sporadic.Co1Schreier.Native.inv
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yield,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  have h1 : ∀ a : Nat, [a:24].size = 24 - a := fun a => by simp [Std.Legacy.Range.size]
  simp only [h1, Nat.sub_zero, ← List.range_eq_range']
  rfl

theorem size_set (M : Array Nat) (i x : Nat) : (M.set! i x).size = M.size := by
  simp [Array.set!]

theorem get_set (M : Array Nat) (i x j : Nat) (hj : j < M.size) :
    (M.set! i x)[j]! = if j = i then x else M[j]! := by
  simp [Array.set!, getElem!_pos, hj, Array.getElem_setIfInBounds, eq_comm]

theorem piv_fold (M : Array Nat) (c : Nat) (l : List Nat) (p0 : Nat) (hl : ∀ r ∈ l, r < 24) :
    (l.foldl (pivStep M c) p0 = p0 ∧ (p0 = 24 → ∀ r ∈ l, (M[r]!).testBit c = false)) ∨
      (p0 = 24 ∧ l.foldl (pivStep M c) p0 ∈ l ∧
        (M[l.foldl (pivStep M c) p0]!).testBit c = true) := by
  induction l generalizing p0 with
  | nil => left; simp
  | cons x l ih =>
    have hl' : ∀ r ∈ l, r < 24 := fun r hr => hl r (List.mem_cons_of_mem x hr)
    have hx : x < 24 := hl x (by simp)
    rw [List.foldl_cons]
    by_cases hp : p0 = 24
    · by_cases ht : (M[x]!).testBit c = true
      · have e : pivStep M c p0 x = x := by simp [pivStep, hp, ht]
        rw [e]
        rcases ih x hl' with ⟨h1, _⟩ | ⟨h1, _⟩
        · right
          rw [h1]
          exact ⟨hp, by simp, ht⟩
        · omega
      · have e : pivStep M c p0 x = p0 := by simp [pivStep, ht]
        rw [e]
        rcases ih p0 hl' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · left
          refine ⟨h1, fun _ r hr => ?_⟩
          rcases List.mem_cons.1 hr with rfl | hr
          · simpa using ht
          · exact h2 hp r hr
        · right
          exact ⟨h1, List.mem_cons_of_mem x h2, h3⟩
    · have e : pivStep M c p0 x = p0 := by simp [pivStep, hp]
      rw [e]
      rcases ih p0 hl' with ⟨h1, _⟩ | ⟨h1, _⟩
      · left
        exact ⟨h1, fun h => absurd h hp⟩
      · exact absurd h1 hp

theorem pivF_spec (M : Array Nat) (c : Nat) :
    (pivF M c < 24 ∧ c ≤ pivF M c ∧ (M[pivF M c]!).testBit c = true) ∨
      (pivF M c = 24 ∧ ∀ r, c ≤ r → r < 24 → (M[r]!).testBit c = false) := by
  have hl : ∀ r ∈ List.range' c (24 - c), r < 24 := fun r hr => by
    rw [List.mem_range'_1] at hr
    omega
  unfold pivF
  rcases piv_fold M c _ 24 hl with ⟨h1, h2⟩ | ⟨_, h2, h3⟩
  · right
    refine ⟨h1, fun r hr1 hr2 => h2 rfl r ?_⟩
    rw [List.mem_range'_1]
    omega
  · left
    rw [List.mem_range'_1] at h2
    exact ⟨by omega, by omega, h3⟩

theorem elim_fold (M : Array Nat) (c rp n : Nat) (hn : n ≤ M.size) :
    ((List.range n).foldl (elimStep c rp) M).size = M.size ∧
      ∀ r < M.size, ((List.range n).foldl (elimStep c rp) M)[r]! =
        if r < n ∧ r ≠ c ∧ (M[r]!).testBit c = true then M[r]! ^^^ rp else M[r]! := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hM' : (List.range n).foldl (elimStep c rp) M = M' at ih1 ih2 ⊢
    have hn' : M'[n]! = M[n]! := by
      rw [ih2 n (by omega)]
      simp
    unfold elimStep
    rw [hn']
    by_cases hb : (n != c && (M[n]!).testBit c) = true
    · rw [ite_eq_left hb]
      simp only [bne_iff_ne, Bool.and_eq_true, ne_eq] at hb
      refine ⟨by rw [size_set, ih1], fun r hr => ?_⟩
      rw [get_set _ _ _ _ (by rw [ih1]; exact hr), ih2 r hr]
      by_cases hrn : r = n
      · subst hrn
        simp [hb]
      · rw [ite_eq_right hrn]
        have e : (r < n + 1) ↔ r < n := by omega
        simp only [e]
    · rw [ite_eq_right hb]
      simp only [bne_iff_ne, Bool.and_eq_true, ne_eq, not_and] at hb
      refine ⟨ih1, fun r hr => ?_⟩
      rw [ih2 r hr]
      by_cases hrn : r = n
      · subst hrn
        by_cases hrc : r = c
        · simp [hrc]
        · have hbit := hb hrc
          simp [hbit]
      · have e : (r < n + 1) ↔ r < n := by omega
        simp only [e]

structure GJ (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) (c : Nat) (M : Array Nat) : Prop where
  size : M.size = 24
  lt : ∀ r < 24, M[r]! < 2 ^ 48
  lin : ∀ r < 24, toVecD 24 M[r]! = toVecD 24 (M[r]! >>> 24) ᵥ* A
  inj : ∀ v : Fin 24 → ZMod 2, (∀ r < 24, toVecD 24 M[r]! ⬝ᵥ v = 0) → v = 0
  piv : ∀ j < c, ∀ r < 24, (M[r]!).testBit j = decide (r = j)

theorem lin_xor {A : Matrix (Fin 24) (Fin 24) (ZMod 2)} {x y : Nat}
    (hx : toVecD 24 x = toVecD 24 (x >>> 24) ᵥ* A) (hy : toVecD 24 y = toVecD 24 (y >>> 24) ᵥ* A) :
    toVecD 24 (x ^^^ y) = toVecD 24 ((x ^^^ y) >>> 24) ᵥ* A := by
  rw [Nat.shiftRight_xor_distrib, toVecD_xor, toVecD_xor, hx, hy, Matrix.add_vecMul]

theorem dot_xor (x y : Nat) (v : Fin 24 → ZMod 2) :
    toVecD 24 (x ^^^ y) ⬝ᵥ v = toVecD 24 x ⬝ᵥ v + toVecD 24 y ⬝ᵥ v := by
  rw [toVecD_xor, add_dotProduct]

theorem toVecD_bit (x : Nat) (k : Fin 24) (b : Bool) (h : x.testBit k.val = b) :
    toVecD 24 x k = if b = true then 1 else 0 := by
  rw [toVecD_apply, h]

theorem GJ_noPiv {A : Matrix (Fin 24) (Fin 24) (ZMod 2)} {c : Nat} {M : Array Nat}
    (h : GJ A c M) (hc : c < 24) (hno : ∀ r, c ≤ r → r < 24 → (M[r]!).testBit c = false) :
    False := by
  let v : Fin 24 → ZMod 2 := fun k =>
    if k.val = c then 1 else if k.val < c then toVecD 24 M[k.val]! ⟨c, hc⟩ else 0
  have hv : v = 0 := by
    apply h.inj v
    intro r hr
    rw [dotProduct]
    by_cases hrc : r < c
    · rw [Fintype.sum_eq_add ⟨c, hc⟩ ⟨r, hr⟩ (by simp [Fin.ext_iff]; omega)]
      · have e1 : toVecD 24 M[r]! ⟨r, hr⟩ = 1 := by
          rw [toVecD_bit _ _ true (by rw [h.piv r hrc r hr]; simp)]
          rfl
        have e2 : v ⟨r, hr⟩ = toVecD 24 M[r]! ⟨c, hc⟩ := by
          simp only [v]
          rw [ite_eq_right (by omega), ite_eq_left hrc]
        have e3 : v ⟨c, hc⟩ = 1 := by simp [v]
        rw [e1, e2, e3, toVecD_apply]
        split <;> decide
      · intro k hk
        simp only [ne_eq, Fin.ext_iff] at hk
        by_cases hkc : k.val < c
        · rw [toVecD_bit _ _ false (by rw [h.piv k hkc r hr]; simp; omega)]
          simp
        · have e : v k = 0 := by
            simp only [v]
            rw [ite_eq_right hk.1, ite_eq_right hkc]
          rw [e, mul_zero]
    · apply Finset.sum_eq_zero
      intro k _
      by_cases hkc : k.val = c
      · rw [toVecD_bit _ _ false (by rw [hkc]; exact hno r (by omega) hr)]
        simp
      · by_cases hkc' : k.val < c
        · rw [toVecD_bit _ _ false (by rw [h.piv k hkc' r hr]; simp; omega)]
          simp
        · have e : v k = 0 := by
            simp only [v]
            rw [ite_eq_right hkc, ite_eq_right hkc']
          rw [e, mul_zero]
  have := congrFun hv ⟨c, hc⟩
  simp [v] at this

theorem GJ_step {A : Matrix (Fin 24) (Fin 24) (ZMod 2)} {c : Nat} {M : Array Nat}
    (h : GJ A c M) (hc : c < 24) : GJ A (c + 1) (stepF M c) := by
  rcases pivF_spec M c with ⟨hp, hcp, hbit⟩ | ⟨_, hno⟩
  swap
  · exact (GJ_noPiv h hc hno).elim
  unfold stepF
  rw [ite_eq_left hp]
  generalize pivF M c = p at hp hcp hbit ⊢
  have hm1 : ∀ r < 24, ((M.set! p M[c]!).set! c M[p]!)[r]! =
      if r = c then M[p]! else if r = p then M[c]! else M[r]! := by
    intro r hr
    rw [get_set _ _ _ _ (by rw [size_set, h.size]; exact hr),
      get_set _ _ _ _ (by rw [h.size]; exact hr)]
  have hs1 : ((M.set! p M[c]!).set! c M[p]!).size = 24 := by rw [size_set, size_set, h.size]
  generalize (M.set! p M[c]!).set! c M[p]! = M1 at hm1 hs1 ⊢
  have he := elim_fold M1 c M[p]! 24 (by omega)
  have hM2 : ∀ r < 24, (elimF M1 c M[p]!)[r]! =
      if r ≠ c ∧ (M1[r]!).testBit c = true then M1[r]! ^^^ M[p]! else M1[r]! := by
    intro r hr
    rw [elimF, he.2 r (by omega)]
    simp [hr]
  have hrp : M1[c]! = M[p]! := by rw [hm1 c hc, ite_eq_left rfl]
  have hrow : ∀ r < 24, ∃ r' < 24, M1[r]! = M[r']! := by
    intro r hr
    rw [hm1 r hr]
    split_ifs
    · exact ⟨p, hp, rfl⟩
    · exact ⟨c, hc, rfl⟩
    · exact ⟨r, hr, rfl⟩
  have piv1 : ∀ j < c, ∀ r < 24, (M1[r]!).testBit j = decide (r = j) := by
    intro j hj r hr
    rw [hm1 r hr]
    split_ifs with h1 h2
    · rw [h.piv j hj p hp]
      simp only [decide_eq_decide]
      omega
    · rw [h.piv j hj c hc]
      simp only [decide_eq_decide]
      omega
    · exact h.piv j hj r hr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [elimF, he.1, hs1]
  · intro r hr
    obtain ⟨r', hr', e⟩ := hrow r hr
    rw [hM2 r hr, e]
    split_ifs
    · exact Nat.xor_lt_two_pow (h.lt r' hr') (h.lt p hp)
    · exact h.lt r' hr'
  · intro r hr
    obtain ⟨r', hr', e⟩ := hrow r hr
    rw [hM2 r hr, e]
    split_ifs
    · exact lin_xor (h.lin r' hr') (h.lin p hp)
    · exact h.lin r' hr'
  · intro v hv
    have h1c : toVecD 24 M1[c]! ⬝ᵥ v = 0 := by
      have := hv c hc
      rw [hM2 c hc, ite_eq_right (by simp)] at this
      exact this
    have h1 : ∀ r < 24, toVecD 24 M1[r]! ⬝ᵥ v = 0 := by
      intro r hr
      have := hv r hr
      rw [hM2 r hr] at this
      split_ifs at this
      · rw [dot_xor, ← hrp, h1c, add_zero] at this
        exact this
      · exact this
    apply h.inj v
    intro r hr
    by_cases hrc : r = c
    · have e : M[r]! = M1[p]! := by
        rw [hm1 p hp, hrc]
        by_cases hpc : p = c
        · simp [hpc]
        · simp [hpc]
      rw [e]
      exact h1 p hp
    · by_cases hrp' : r = p
      · rw [hrp', ← hrp]
        exact h1 c hc
      · have e : M[r]! = M1[r]! := by rw [hm1 r hr, ite_eq_right hrc, ite_eq_right hrp']
        rw [e]
        exact h1 r hr
  · intro j hj r hr
    rw [hM2 r hr]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · split_ifs
      · rw [Nat.testBit_xor, piv1 j hj r hr, ← hrp, piv1 j hj c hc]
        have : c ≠ j := by omega
        simp [this]
      · exact piv1 j hj r hr
    · subst hj
      split_ifs with hh
      · rw [Nat.testBit_xor, hh.2, hbit]
        simp [hh.1]
      · by_cases hrc : r = j
        · subst hrc
          rw [hrp, hbit]
          simp
        · have hb : (M1[r]!).testBit j = false := by
            simpa [hrc] using hh
          rw [hb]
          simp [hrc]

theorem GJ_fold {A : Matrix (Fin 24) (Fin 24) (ZMod 2)} {M : Array Nat} (h : GJ A 0 M) :
    ∀ n ≤ 24, GJ A n ((List.range n).foldl stepF M) := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact GJ_step (ih (by omega)) (by omega)

theorem initF_get (X : Rows) (r : Nat) (hr : r < 24) :
    (initF X)[r]! = (X[r]?.getD 0) % 2 ^ 24 ||| (1 <<< (24 + r)) := by
  simp [initF, getElem!_pos, hr]

theorem GJ_init (X : Rows) (hA : ∀ v, rowsMatrix 24 X *ᵥ v = 0 → v = 0) :
    GJ (rowsMatrix 24 X) 0 (initF X) := by
  have hleft : ∀ r (hr : r < 24), toVecD 24 (initF X)[r]! = rowsMatrix 24 X ⟨r, hr⟩ := by
    intro r hr
    funext j
    rw [initF_get X r hr, rowsMatrix_apply, toVecD_apply, toVecD_apply, Nat.testBit_or,
      Nat.testBit_mod_two_pow, Nat.one_shiftLeft, Nat.testBit_two_pow]
    have h1 : j.val < 24 := j.isLt
    have h2 : ¬ (24 + r = j.val) := by omega
    simp [h1, h2]
  refine ⟨by simp [initF], ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  · intro r hr
    rw [initF_get X r hr]
    refine Nat.or_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 24))
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))) ?_
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · intro r hr
    have hsh : (initF X)[r]! >>> 24 = 1 <<< r := by
      rw [initF_get X r hr]
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.one_shiftLeft,
        Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.testBit_two_pow]
      have : ¬ (24 + i < 24) := by omega
      simp only [this, decide_false, Bool.false_and, Bool.false_or]
      by_cases hri : r = i
      · subst hri
        simp
      · simp [hri]
    have hsingle : toVecD 24 (1 <<< r) = Pi.single (⟨r, hr⟩ : Fin 24) 1 := by
      funext j
      rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow, Pi.single_apply]
      by_cases hj : j = ⟨r, hr⟩
      · subst hj
        simp
      · have : r ≠ j.val := fun e => hj (Fin.ext e.symm)
        simp [hj, this]
    rw [hleft r hr, hsh, hsingle, Matrix.single_one_vecMul]
    rfl
  · intro v hv
    apply hA v
    funext i
    have := hv i.val i.isLt
    rw [hleft i.val i.isLt] at this
    exact this

theorem inv_eq_of_mul {X Y : Rows} (h : rowsMatrix 24 X * rowsMatrix 24 Y = 1)
    (hY : Y.size = 24) (hYr : ∀ i < 24, Y[i]?.getD 0 < 2 ^ 24) :
    CFSG.Sporadic.Co1Schreier.Native.inv X = Y := by
  have hBA : rowsMatrix 24 Y * rowsMatrix 24 X = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin 24) (Fin 24) (ZMod 2) rfl).mp h
  have hA : ∀ v, rowsMatrix 24 X *ᵥ v = 0 → v = 0 := fun v hv => by
    rw [← Matrix.one_mulVec v, ← hBA, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hF := GJ_fold (GJ_init X hA) 24 le_rfl
  rw [inv_eq_invF]
  unfold invF
  generalize (List.range 24).foldl stepF (initF X) = F at hF ⊢
  have hrow : ∀ i : Fin 24, rowsMatrix 24 (F.map (· >>> 24)) i = toVecD 24 (F[i.val]! >>> 24) := by
    intro i
    funext k
    have hi : i.val < F.size := by rw [hF.size]; exact i.isLt
    rw [rowsMatrix_apply, Array.getElem?_map, Array.getElem?_eq_getElem hi, Option.map_some,
      Option.getD_some, getElem!_pos F i.val hi]
  have hR : rowsMatrix 24 (F.map (· >>> 24)) * rowsMatrix 24 X = 1 := by
    ext i j
    rw [Matrix.mul_apply', Matrix.one_apply, hrow i]
    change (toVecD 24 (F[i.val]! >>> 24) ᵥ* rowsMatrix 24 X) j = _
    rw [← hF.lin i.val i.isLt, toVecD_apply, hF.piv j.val j.isLt i.val i.isLt]
    by_cases hij : i = j
    · subst hij
      simp
    · have : i.val ≠ j.val := fun e => hij (Fin.ext e)
      simp [hij, this]
  have hRB : rowsMatrix 24 (F.map (· >>> 24)) = rowsMatrix 24 Y := by
    calc rowsMatrix 24 (F.map (· >>> 24))
        = rowsMatrix 24 (F.map (· >>> 24)) * (rowsMatrix 24 X * rowsMatrix 24 Y) := by
          rw [h, Matrix.mul_one]
      _ = rowsMatrix 24 (F.map (· >>> 24)) * rowsMatrix 24 X * rowsMatrix 24 Y :=
          (Matrix.mul_assoc _ _ _).symm
      _ = rowsMatrix 24 Y := by rw [hR, Matrix.one_mul]
  apply Array.ext
  · rw [Array.size_map, hF.size, hY]
  · intro i h1 h2
    have hi : i < 24 := by rw [Array.size_map, hF.size] at h1; exact h1
    have hiF : i < F.size := by rw [hF.size]; exact hi
    have hYi : Y[i]?.getD 0 = Y[i] := by rw [Array.getElem?_eq_getElem h2, Option.getD_some]
    rw [Array.getElem_map]
    have hFi : F[i] = F[i]! := (getElem!_pos F i hiF).symm
    rw [hFi]
    apply toVecD_injective (d := 24)
    · rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hF.lt i hi)
    · rw [← hYi]
      exact hYr i hi
    · have e := congrFun hRB ⟨i, hi⟩
      rw [hrow ⟨i, hi⟩] at e
      rw [e, ← hYi]
      rfl

theorem invOK_of {X Y : Nat} (h : invOKK X Y = true) :
    mul (unpack 24 24 X) (unpack 24 24 Y) = one () ∧
      CFSG.Sporadic.Co1Schreier.Native.inv (unpack 24 24 X) = unpack 24 24 Y := by
  have e : mulK X Y = idM := Nat.eq_of_beq_eq_true h
  have hm : mul (unpack 24 24 X) (unpack 24 24 Y) = one () := by
    rw [← unpack_mulK, e, unpack_idM]
  refine ⟨hm, inv_eq_of_mul ?_ (unpack_size Y) (fun i hi => by rw [unpack_getD Y i hi]; exact rowV_lt Y i)⟩
  rw [← rowsMatrix_mulRows]
  change rowsMatrix 24 (mul (unpack 24 24 X) (unpack 24 24 Y)) = 1
  rw [hm]
  exact rowsMatrix_idRows 24

@[expose] noncomputable def rowsL (M : Nat → Nat) (k : Nat) : List Rows :=
  (List.range k).map fun i => unpack 24 24 (M i)

theorem rowsL_succ (M : Nat → Nat) (k : Nat) :
    rowsL M k ++ [unpack 24 24 (M k)] = rowsL M (k + 1) := by
  simp [rowsL, List.range_succ]

theorem dag_fold {α : Type} {M MI : Nat → Nat} {N : Nat} (ok : Nat → List α → Bool)
    (val : List α → Nat) (dec : List α → List Int)
    (hw : ∀ k w, ok k w = true → word (rowsL M k) (rowsL MI k) (dec w) = unpack 24 24 (val w))
    (hinv : ∀ i < N, invOKK (M i) (MI i) = true) :
    ∀ (ws : List (List α)) (k : Nat), k + ws.length ≤ N →
      List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun w _ ih k => bAnd(ok k w, bAnd(Nat.beq (val w) (M k), ih (Nat.succ k)))) ws k = true →
      (ws.map dec).foldl step (rowsL M k, rowsL MI k, true) =
        (rowsL M (k + ws.length), rowsL MI (k + ws.length), true) := by
  intro ws
  induction ws with
  | nil => intro k _ _; rfl
  | cons w ws ih =>
    intro k hk hrec
    simp only [bAnd_eq, Bool.and_eq_true] at hrec
    obtain ⟨h1, h2, h3⟩ := hrec
    simp only [List.length_cons] at hk
    obtain ⟨hm, hi⟩ := invOK_of (hinv k (by omega))
    have hs : step (rowsL M k, rowsL MI k, true) (dec w) = (rowsL M (k + 1), rowsL MI (k + 1), true) := by
      unfold step
      simp only
      rw [hw k w h1, Nat.eq_of_beq_eq_true h2, hi, hm, rowsL_succ, rowsL_succ, beq_self_eq_true,
        Bool.and_true]
    rw [List.map_cons, List.foldl_cons, hs,
      ih (k + 1) (by omega) (by simpa only [bAnd_eq, Nat.succ_eq_add_one] using h3), List.length_cons,
      show k + 1 + ws.length = k + (ws.length + 1) by omega]

theorem dag_sound {α : Type} {M MI : Nat → Nat} {nb N : Nat} (ok : Nat → List α → Bool)
    (val : List α → Nat) (dec : List α → List Int) {ws : List (List α)} {base : List Rows}
    (hb : base = rowsL M nb)
    (hw : ∀ k w, ok k w = true → word (rowsL M k) (rowsL MI k) (dec w) = unpack 24 24 (val w))
    (hN : nb + ws.length = N) (hinv : ∀ i < N, invOKK (M i) (MI i) = true)
    (hrec : List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun w _ ih k => bAnd(ok k w, bAnd(Nat.beq (val w) (M k), ih (Nat.succ k)))) ws nb = true) :
    dag base (ws.map dec) = (rowsL M N, rowsL MI N, true) := by
  have hmap : base.map CFSG.Sporadic.Co1Schreier.Native.inv = rowsL MI nb := by
    rw [hb, rowsL, rowsL, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (invOK_of (hinv i (by rw [List.mem_range] at hi; omega))).2
  have hall : (base.all fun b => mul b (CFSG.Sporadic.Co1Schreier.Native.inv b) == one ()) = true := by
    rw [List.all_eq_true]
    intro b hbm
    rw [hb, rowsL, List.mem_map] at hbm
    obtain ⟨i, hi, rfl⟩ := hbm
    obtain ⟨hm, hinv'⟩ := invOK_of (hinv i (by rw [List.mem_range] at hi; omega))
    rw [hinv', hm]
    exact beq_self_eq_true _
  unfold dag
  rw [hmap, hall, hb, dag_fold ok val dec hw hinv ws nb (by omega) hrec, hN]

end CFSG.KS.SporSch.M24.MatL

end
