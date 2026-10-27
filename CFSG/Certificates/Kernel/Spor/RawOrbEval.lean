module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = (if c = true then t else e) := by
  cases c <;> rfl

theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = (if c = true then t else e) := by
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
    rw [hs, strictN_eq, ih, foldBlk_eq, shiftLeft_six h,
      Nat.add_one_mul h 64, foldr_range_add f (h * 64) 64 x]

theorem foldN_eq (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = (List.range n).foldr f s := by
  refine Eq.trans (foldN_rec_eq f (Nat.shiftRight n (nat_lit 6))
    (foldBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) s)) ?_
  rw [foldBlk_eq, shiftLeft_six, land_63, shiftRight_six,
    ← foldr_range_add f (n / 64 * 64) (n % 64) s, Nat.div_add_mod' n 64]

theorem foldr_range_succ (h : Nat → Nat → Nat) (k s : Nat) :
    (List.range (k + 1)).foldr h s = h 0 ((List.range k).foldr (fun x y => h (Nat.succ x) y) s) := by
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
    rw [hs, ih, allBlk_eq, shiftLeft_six h, Nat.add_one_mul h 64,
      all_range_add f (h * 64) 64, Bool.and_comm]

theorem allN_eq (n : Nat) (f : Nat → Bool) : allN n f = (List.range n).all f := by
  have hs : allN n f = (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) &&
        Nat.rec (motive := fun _ => Bool) true
          (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
            (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64)))
          (Nat.shiftRight n (nat_lit 6))) :=
    rfl
  rw [hs, allN_rec_eq, allBlk_eq, shiftLeft_six, land_63, shiftRight_six, Bool.and_comm,
    ← all_range_add f (n / 64 * 64) (n % 64), Nat.div_add_mod' n 64]

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  rw [allN_eq, List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.2 hi), fun h x hx => h x (List.mem_range.1 hx)⟩

theorem mask_eq' (w : Nat) : mask w = 2 ^ w - 1 := by
  change (1 <<< w) - 1 = 2 ^ w - 1
  rw [Nat.one_shiftLeft]

theorem land_mask (x w : Nat) : Nat.land x (mask w) = x % 2 ^ w := by
  rw [mask_eq']
  exact Nat.and_two_pow_sub_one_eq_mod x w

theorem fld_eq (x o w : Nat) : Nat.land (Nat.shiftRight x o) (mask w) = x / 2 ^ o % 2 ^ w := by
  have e : Nat.shiftRight x o = x / 2 ^ o := Nat.shiftRight_eq_div_pow x o
  rw [e, land_mask]

theorem pg_eq (w p i : Nat) : pg w (mask w) p i = p / 2 ^ (w * i) % 2 ^ w :=
  fld_eq p (w * i) w

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
    rw [h0] <;> rfl
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

end CFSG.KS.Raw.Orb

end
