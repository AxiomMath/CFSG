module

public import CFSG.Certificates.Kernel.O8OrthDefs
public import Certificates.Data.Kernel.O8.Orth
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.O8.OrthPf

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.O8
  CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by cases c <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem pw2_eq (x : Nat) : pw2 x = 2 ^ x := by
  change 1 <<< x = 2 ^ x
  rw [Nat.one_shiftLeft]

theorem maskN_eq (w : Nat) : maskN w = 2 ^ w - 1 := by
  change pw2 w - 1 = _
  rw [pw2_eq]

theorem fget_eq (X i w : Nat) : fget X i w = X >>> (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& maskN w = _
  rw [maskN_eq, Nat.and_two_pow_sub_one_eq_mod]

theorem testBit_fget (X i w j : Nat) :
    (fget X i w).testBit j = (decide (j < w) && X.testBit (i * w + j)) := by
  rw [fget_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem fget_lt (X i w : Nat) : fget X i w < 2 ^ w := by
  rw [fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem bitN_eq (x i : Nat) : bitN x i = (x.testBit i).toNat := by
  change (x >>> i) &&& 1 = _
  have e : x.testBit i = (x >>> i).testBit 0 := by rw [Nat.testBit_shiftRight, Nat.add_zero]
  rw [Nat.and_one_is_mod, e, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h | h <;> rw [h] <;> rfl

theorem beq_bitN (x i : Nat) : Nat.beq (bitN x i) 1 = x.testBit i := by
  rw [bitN_eq]
  cases x.testBit i <;> rfl

theorem xor_toNat (a b : Bool) : Nat.xor a.toNat b.toNat = (a ^^ b).toNat := by
  cases a <;> cases b <;> rfl

theorem beq_toNat_one (a : Bool) : Nat.beq a.toNat 1 = a := by cases a <;> rfl

theorem testBit_orN_iff (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (orN n f).testBit p = true ↔ ∃ i < n, (f i).testBit p = true
  | 0 => by
    have e : orN 0 f = 0 := rfl
    simp [e]
  | n + 1 => by
    have e : orN (n + 1) f = f n ||| orN n f := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, testBit_orN_iff f p n]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem allN_eq (n : Nat) (f : Nat → Bool) : allN n f = (List.range n).all f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change andB (f n) (allN n f) = _
    rw [andB_eq, ih, List.range_succ, List.all_append, Bool.and_comm]
    simp

theorem sumN_ind (n : Nat) (p : Nat → Bool) :
    sumN n (fun z => nIf(p z, nat_lit 1, nat_lit 0)) = ((List.range n).filter p).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change nIf(p n, nat_lit 1, nat_lit 0) + sumN n _ = _
    rw [ih, List.range_succ, List.filter_append, List.length_append, nIf_eq]
    cases h : p n <;> simp [h, Nat.add_comm]

inductive InSp (S : ℕ → Prop) : ℕ → Prop
  | zero : InSp S 0
  | add {a b : ℕ} : S a → InSp S b → InSp S (a ^^^ b)

theorem InSp.of_mem {S : ℕ → Prop} {a : ℕ} (h : S a) : InSp S a := by
  have := InSp.add h InSp.zero
  rwa [Nat.xor_zero] at this

theorem InSp.xor {S : ℕ → Prop} {a b : ℕ} (ha : InSp S a) (hb : InSp S b) : InSp S (a ^^^ b) := by
  induction ha with
  | zero => rwa [Nat.zero_xor]
  | add hs _ ih =>
    rw [Nat.xor_assoc]
    exact InSp.add hs ih

theorem InSp.mono {S T : ℕ → Prop} (h : ∀ a, S a → InSp T a) {x : ℕ} (hx : InSp S x) :
    InSp T x := by
  induction hx with
  | zero => exact InSp.zero
  | add hs _ ih => exact (h _ hs).xor ih

theorem InSp.lt {S : ℕ → Prop} {n : ℕ} (hS : ∀ a, S a → a < 2 ^ n) {x : ℕ} (hx : InSp S x) :
    x < 2 ^ n := by
  induction hx with
  | zero => exact Nat.two_pow_pos n
  | add hs _ ih => exact Nat.xor_lt_two_pow (hS _ hs) ih

theorem InSp.empty {x : ℕ} (hx : InSp (fun _ => False) x) : x = 0 := by
  induction hx with
  | zero => rfl
  | add hs _ _ => exact hs.elim

theorem xor_xor_cancel (a b : ℕ) : a ^^^ b ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem InSp.insert_iff {S : ℕ → Prop} {v x : ℕ} :
    InSp (fun a => S a ∨ a = v) x ↔ InSp S x ∨ InSp S (x ^^^ v) := by
  constructor
  · intro hx
    induction hx with
    | zero => exact Or.inl InSp.zero
    | @add a b hs _ ih =>
      rcases hs with hs | hs
      · rcases ih with ih | ih
        · exact Or.inl (InSp.add hs ih)
        · right
          rw [Nat.xor_assoc]
          exact InSp.add hs ih
      · subst hs
        rcases ih with ih | ih
        · right
          rwa [Nat.xor_comm a b, xor_xor_cancel]
        · left
          rwa [Nat.xor_comm]
  · rintro (h | h)
    · exact InSp.mono (fun a ha => InSp.of_mem (Or.inl ha)) h
    · have h1 : InSp (fun a => S a ∨ a = v) (x ^^^ v) :=
        InSp.mono (fun a ha => InSp.of_mem (Or.inl ha)) h
      have h2 : InSp (fun a => S a ∨ a = v) v := InSp.of_mem (Or.inr rfl)
      have := h1.xor h2
      rwa [xor_xor_cancel] at this

theorem InSp.insert_of_mem {S : ℕ → Prop} {v x : ℕ} (hv : InSp S v) :
    InSp (fun a => S a ∨ a = v) x ↔ InSp S x := by
  rw [InSp.insert_iff]
  constructor
  · rintro (h | h)
    · exact h
    · have := h.xor hv
      rwa [xor_xor_cancel] at this
  · exact Or.inl

theorem InSp.insert_swap {S : ℕ → Prop} {r v x : ℕ} (h : InSp S (r ^^^ v)) :
    InSp (fun a => S a ∨ a = r) x ↔ InSp (fun a => S a ∨ a = v) x := by
  rw [InSp.insert_iff, InSp.insert_iff]
  have e1 : x ^^^ r = x ^^^ v ^^^ (r ^^^ v) := by
    rw [Nat.xor_assoc, ← Nat.xor_assoc v, Nat.xor_comm v r, Nat.xor_assoc, Nat.xor_self,
      Nat.xor_zero]
  have e2 : x ^^^ v = x ^^^ r ^^^ (r ^^^ v) := by
    rw [Nat.xor_assoc, ← Nat.xor_assoc r, Nat.xor_self, Nat.zero_xor]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl h1
    · right
      rw [e2]
      exact h1.xor h
  · rintro (h1 | h1)
    · exact Or.inl h1
    · right
      rw [e1]
      exact h1.xor h

open Classical in
noncomputable def spanF (S : ℕ → Prop) : Finset ℕ := (Finset.range 64).filter (InSp S)

theorem mem_spanF {S : ℕ → Prop} {x : ℕ} : x ∈ spanF S ↔ x < 64 ∧ InSp S x := by
  classical
  simp [spanF]

theorem spanF_congr {S T : ℕ → Prop} (h : ∀ x, InSp S x ↔ InSp T x) : spanF S = spanF T := by
  ext x
  rw [mem_spanF, mem_spanF, h]

theorem card_spanF_empty : (spanF fun _ => False).card = 1 := by
  have : spanF (fun _ => False) = {0} := by
    ext x
    rw [mem_spanF, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact h.empty
    · rintro rfl
      exact ⟨by omega, InSp.zero⟩
  rw [this, Finset.card_singleton]

theorem card_spanF_insert {S : ℕ → Prop} {v : ℕ} (hS : ∀ a, S a → a < 64) (hv : v < 64)
    (hn : ¬ InSp S v) : (spanF fun a => S a ∨ a = v).card = 2 * (spanF S).card := by
  classical
  have hS' : ∀ a, S a → a < 2 ^ 6 := hS
  have hv' : v < 2 ^ 6 := hv
  have e : spanF (fun a => S a ∨ a = v) = spanF S ∪ (spanF S).image (· ^^^ v) := by
    ext x
    rw [mem_spanF, Finset.mem_union, Finset.mem_image, mem_spanF, InSp.insert_iff]
    constructor
    · rintro ⟨hx, h | h⟩
      · exact Or.inl ⟨hx, h⟩
      · refine Or.inr ⟨x ^^^ v, ?_, xor_xor_cancel x v⟩
        rw [mem_spanF]
        exact ⟨InSp.lt hS' h, h⟩
    · rintro (⟨hx, h⟩ | ⟨y, hy, rfl⟩)
      · exact ⟨hx, Or.inl h⟩
      · rw [mem_spanF] at hy
        refine ⟨Nat.xor_lt_two_pow (n := 6) hy.1 hv', Or.inr ?_⟩
        rw [xor_xor_cancel]
        exact hy.2
  have hd : Disjoint (spanF S) ((spanF S).image (· ^^^ v)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_image] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    rw [mem_spanF] at hx hy
    apply hn
    have := hy.2.xor hx.2
    rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
  have hi : Function.Injective (· ^^^ v : ℕ → ℕ) := by
    intro a b h
    have := congrArg (· ^^^ v) h
    simpa [xor_xor_cancel] using this
  rw [e, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hi, Nat.two_mul]

theorem rankParAux_spec : ∀ (vs sp : List ℕ) (S : ℕ → Prop) (b : Bool),
    (∀ a, S a → a < 64) → (∀ v ∈ vs, v < 64) → (∀ x, x ∈ sp ↔ InSp S x) →
    ∃ c, rankParAux sp vs b = (b ^^ decide (c % 2 = 1)) ∧
      (spanF fun a => S a ∨ a ∈ vs).card = 2 ^ c * (spanF S).card
  | [], sp, S, b, _, _, _ => by
    refine ⟨0, by simp [rankParAux], ?_⟩
    have : (fun a => S a ∨ a ∈ ([] : List ℕ)) = S := by
      funext a
      simp
    rw [this, pow_zero, Nat.one_mul]
  | v :: vs, sp, S, b, hS, hvs, hsp => by
    have hv : v < 64 := hvs v (by simp)
    have hvs' : ∀ w ∈ vs, w < 64 := fun w hw => hvs w (by simp [hw])
    have hS' : ∀ a, (S a ∨ a = v) → a < 64 := by
      rintro a (h | rfl)
      · exact hS a h
      · exact hv
    have epred : (fun a => S a ∨ a ∈ v :: vs) = fun a => (S a ∨ a = v) ∨ a ∈ vs := by
      funext a
      apply propext
      simp only [List.mem_cons]
      tauto
    rw [epred]
    by_cases hc : sp.contains v = true
    · have hin : InSp S v := (hsp v).1 (by simpa using hc)
      obtain ⟨c, h1, h2⟩ := rankParAux_spec vs sp (fun a => S a ∨ a = v) b hS' hvs'
        (fun x => by rw [hsp x, InSp.insert_of_mem hin])
      refine ⟨c, ?_, ?_⟩
      · rw [rankParAux, if_pos hc, h1]
      · rw [h2, spanF_congr (fun x => InSp.insert_of_mem hin)]
    · have hn : ¬ InSp S v := fun h => hc (by simpa using (hsp v).2 h)
      obtain ⟨c, h1, h2⟩ := rankParAux_spec vs (sp ++ sp.map (· ^^^ v)) (fun a => S a ∨ a = v)
        (!b) hS' hvs' (fun x => by
          rw [InSp.insert_iff, List.mem_append, List.mem_map, hsp x]
          constructor
          · rintro (h | ⟨y, hy, rfl⟩)
            · exact Or.inl h
            · right
              rw [xor_xor_cancel]
              exact (hsp y).1 hy
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr ⟨x ^^^ v, (hsp _).2 h, xor_xor_cancel x v⟩)
      refine ⟨c + 1, ?_, ?_⟩
      · rw [rankParAux, if_neg hc, h1]
        cases b <;> rcases Nat.mod_two_eq_zero_or_one c with h | h <;>
          simp [h, Nat.succ_mod_two_eq_one_iff, Nat.succ_mod_two_eq_zero_iff]
      · rw [h2, card_spanF_insert hS hv hn, pow_succ]
        ring

theorem dickC_spec {L : List ℕ} (hL : ∀ j < 6, L.getD j 0 < 64) :
    ∃ c, dickC L = decide (c % 2 = 1) ∧
      (spanF fun a => ∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j).card = 2 ^ c := by
  have hvs : ∀ v ∈ (List.range 6).map (fun j => L.getD j 0 ^^^ 2 ^ j), v < 64 := by
    intro v hv
    simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    have h1 : L.getD j 0 < 2 ^ 6 := hL j hj
    have h2 : 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right (by omega) hj
    exact Nat.xor_lt_two_pow h1 h2
  obtain ⟨c, h1, h2⟩ := rankParAux_spec ((List.range 6).map fun j => L.getD j 0 ^^^ 2 ^ j) [0]
    (fun _ => False) false (fun _ h => h.elim) hvs (fun x => by
      rw [List.mem_singleton]
      exact ⟨fun h => h ▸ InSp.zero, fun h => h.empty⟩)
  refine ⟨c, by rw [dickC, h1]; simp, ?_⟩
  rw [card_spanF_empty, Nat.mul_one] at h2
  have e : (fun a => ∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j) =
      fun a => False ∨ a ∈ (List.range 6).map fun j => L.getD j 0 ^^^ 2 ^ j := by
    funext a
    apply propext
    simp only [false_or, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, h⟩
      exact ⟨j, hj, h.symm⟩
  rw [e, h2]

@[expose] noncomputable def redF (P v : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) v (fun b ih2 => strictN ih2 fun u =>
    (fun t => nIf(Nat.beq (bitN u t) (nat_lit 1), Nat.xor u (fget P t (nat_lit 6)), u))
      (Nat.sub (nat_lit 5) b)) n

@[expose] noncomputable def dRec (C : ℕ) (n : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun j ih P => (fun v => (fun r => nIf(Nat.beq r (nat_lit 0), ih P,
          Nat.add (nat_lit 1) (ih (Nat.lor P (Nat.shiftLeft r (Nat.mul (nat_lit 6) (lead6 r)))))))
        (redF P v 6))
      (Nat.xor (colAt C j) (pw2 j))) n

theorem dickK_eq (C : ℕ) : dickK C = dRec C 6 0 % 2 := by
  change Nat.land (dRec C 6 0) 1 = _
  exact Nat.and_one_is_mod _

theorem redF_succ (P v n : ℕ) : redF P v (n + 1) =
    if (redF P v n).testBit (5 - n) = true then redF P v n ^^^ fget P (5 - n) 6
    else redF P v n := by
  change strictN (redF P v n) (fun u => (fun t => nIf(Nat.beq (bitN u t) (nat_lit 1),
    Nat.xor u (fget P t (nat_lit 6)), u)) (Nat.sub (nat_lit 5) n)) = _
  rw [strictN_eq]
  beta_reduce
  rw [nIf_eq, beq_bitN]
  rfl

theorem dRec_succ (C j P : ℕ) : dRec C (j + 1) P =
    if redF P (colAt C j ^^^ 2 ^ j) 6 = 0 then dRec C j P
    else 1 + dRec C j (P ||| redF P (colAt C j ^^^ 2 ^ j) 6 <<< (6 * lead6
      (redF P (colAt C j ^^^ 2 ^ j) 6))) := by
  change nIf(Nat.beq (redF P (Nat.xor (colAt C j) (pw2 j)) 6) (nat_lit 0), dRec C j P,
    Nat.add (nat_lit 1) (dRec C j (Nat.lor P (Nat.shiftLeft (redF P (Nat.xor (colAt C j) (pw2 j)) 6)
      (Nat.mul (nat_lit 6) (lead6 (redF P (Nat.xor (colAt C j) (pw2 j)) 6))))))) = _
  rw [nIf_eq, pw2_eq]
  change (if Nat.beq (redF P (colAt C j ^^^ 2 ^ j) 6) 0 = true then dRec C j P
    else 1 + dRec C j (P ||| redF P (colAt C j ^^^ 2 ^ j) 6 <<< (6 * lead6
      (redF P (colAt C j ^^^ 2 ^ j) 6)))) = _
  by_cases h : redF P (colAt C j ^^^ 2 ^ j) 6 = 0
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · rw [if_neg h, if_neg (fun h' => h (Nat.eq_of_beq_eq_true h'))]

@[expose] def PivOK (P : ℕ) : Prop :=
  ∀ t < 6, fget P t 6 = 0 ∨ ((fget P t 6).testBit t = true ∧ fget P t 6 < 2 ^ (t + 1))

@[expose] def PivSet (P n : ℕ) : ℕ → Prop := fun a => ∃ t < n, a = fget P t 6

theorem lead6_spec : ∀ r < 64, r ≠ 0 →
    lead6 r < 6 ∧ r.testBit (lead6 r) = true ∧ r < 2 ^ (lead6 r + 1) := by
  decide +kernel

theorem pivSet_zero (P : ℕ) {x : ℕ} (h : InSp (PivSet P 0) x) : x = 0 :=
  (InSp.mono (T := fun _ => False) (fun _ ⟨_, ht, _⟩ => absurd ht (Nat.not_lt_zero _)) h).empty

theorem piv_zero {P : ℕ} (hP : PivOK P) : ∀ n ≤ 6, ∀ x, InSp (PivSet P n) x →
    (∀ t < n, fget P t 6 ≠ 0 → x.testBit t = false) → x = 0
  | 0, _, x, hx, _ => pivSet_zero P hx
  | n + 1, hn, x, hx, hb => by
    have e : PivSet P (n + 1) = fun a => PivSet P n a ∨ a = fget P n 6 := by
      funext a
      apply propext
      constructor
      · rintro ⟨t, ht, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · exact Or.inl ⟨t, ht, rfl⟩
        · exact Or.inr rfl
      · rintro (⟨t, ht, rfl⟩ | rfl)
        · exact ⟨t, by omega, rfl⟩
        · exact ⟨n, by omega, rfl⟩
    have hlt : ∀ a, PivSet P n a → a < 2 ^ n := by
      rintro a ⟨t, ht, rfl⟩
      rcases hP t (by omega) with h | ⟨_, h⟩
      · rw [h]
        exact Nat.two_pow_pos n
      · exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))
    have ih := piv_zero hP n (by omega)
    rw [e, InSp.insert_iff] at hx
    rcases hx with hx | hx
    · exact ih x hx fun t ht => hb t (by omega)
    · by_cases h0 : fget P n 6 = 0
      · rw [h0, Nat.xor_zero] at hx
        exact ih x hx fun t ht => hb t (by omega)
      · exfalso
        have h1 : (x ^^^ fget P n 6).testBit n = false := Nat.testBit_lt_two_pow (InSp.lt hlt hx)
        have h2 : (fget P n 6).testBit n = true := by
          rcases hP n (by omega) with h | ⟨h, _⟩
          · exact absurd h h0
          · exact h
        rw [Nat.testBit_xor, hb n (by omega) h0, h2] at h1
        exact absurd h1 (by decide)

theorem redF_spec {P v : ℕ} (hP : PivOK P) (hv : v < 64) : ∀ n ≤ 6,
    redF P v n < 64 ∧ InSp (PivSet P 6) (redF P v n ^^^ v) ∧
      ∀ t, 6 - n ≤ t → t < 6 → fget P t 6 ≠ 0 → (redF P v n).testBit t = false
  | 0, _ => by
    refine ⟨hv, ?_, fun t ht ht' _ => by omega⟩
    change InSp _ (v ^^^ v)
    rw [Nat.xor_self]
    exact InSp.zero
  | n + 1, hn => by
    obtain ⟨h1, h2, h3⟩ := redF_spec hP hv n (by omega)
    have hF : fget P (5 - n) 6 < 2 ^ 6 := fget_lt _ _ _
    have h1' : redF P v n < 2 ^ 6 := h1
    rw [redF_succ]
    split
    · rename_i hb
      refine ⟨Nat.xor_lt_two_pow h1' hF, ?_, ?_⟩
      · have : redF P v n ^^^ fget P (5 - n) 6 ^^^ v =
            fget P (5 - n) 6 ^^^ (redF P v n ^^^ v) := by
          rw [Nat.xor_comm (redF P v n), Nat.xor_assoc]
        rw [this]
        exact InSp.add ⟨5 - n, by omega, rfl⟩ h2
      · intro t ht ht' h0
        rw [Nat.testBit_xor]
        rcases Nat.lt_or_ge t (5 - n + 1) with htt | htt
        · have : t = 5 - n := by omega
          subst this
          rcases hP (5 - n) (by omega) with h | ⟨h, _⟩
          · exact absurd h h0
          · rw [hb, h]
            rfl
        · rw [h3 t (by omega) ht' h0]
          rcases hP (5 - n) (by omega) with h | ⟨_, h⟩
          · rw [h]
            simp
          · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) htt))]
            rfl
    · rename_i hb
      refine ⟨h1, h2, ?_⟩
      intro t ht ht' h0
      rcases Nat.lt_or_ge t (5 - n + 1) with htt | htt
      · have : t = 5 - n := by omega
        subst this
        simpa using hb
      · exact h3 t (by omega) ht' h0

theorem fget_lor_shl {P r l : ℕ} (hl0 : fget P l 6 = 0) (hr : r < 64) (t : ℕ) :
    fget (P ||| r <<< (6 * l)) t 6 = if t = l then r else fget P t 6 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fget, Nat.testBit_or, Nat.testBit_shiftLeft]
  have hr' : r < 2 ^ 6 := hr
  by_cases ht : t = l
  · subst ht
    rw [if_pos rfl]
    have h0 : P.testBit (t * 6 + i) = (decide (i < 6) && P.testBit (t * 6 + i)) ∨ ¬ i < 6 := by
      by_cases hi : i < 6
      · left
        simp [hi]
      · right
        exact hi
    by_cases hi : i < 6
    · have hz := congrArg (fun x => x.testBit i) hl0
      simp only [testBit_fget, Nat.zero_testBit, hi, decide_true, Bool.true_and] at hz
      rw [hz]
      have e : t * 6 + i - 6 * t = i := by omega
      simp [hi, e, show t * 6 + i ≥ 6 * t by omega]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr' (Nat.pow_le_pow_right (by omega)
        (by omega : 6 ≤ i)))]
      simp [hi]
  · rw [if_neg ht, testBit_fget]
    by_cases hi : i < 6
    · rcases Nat.lt_or_gt_of_ne ht with htl | htl
      · have : ¬ (t * 6 + i ≥ 6 * l) := by omega
        simp [hi, this]
      · have hb : r.testBit (t * 6 + i - 6 * l) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr' (Nat.pow_le_pow_right (by omega)
            (by omega)))
        simp [hi, hb]
    · simp [hi]

theorem dRec_spec (C : ℕ) : ∀ n ≤ 6, ∀ (P : ℕ) (S : ℕ → Prop), PivOK P →
    (∀ a, S a → a < 64) → (∀ x, InSp (PivSet P 6) x ↔ InSp S x) →
    (spanF fun a => S a ∨ ∃ j < n, a = colAt C j ^^^ 2 ^ j).card =
      2 ^ dRec C n P * (spanF S).card
  | 0, _, P, S, _, _, _ => by
    have : (fun a => S a ∨ ∃ j < 0, a = colAt C j ^^^ 2 ^ j) = S := by
      funext a
      simp
    rw [this]
    simp [dRec]
  | n + 1, hn, P, S, hP, hS, hsp => by
    have hv : colAt C n ^^^ 2 ^ n < 64 := by
      have h1 : colAt C n < 2 ^ 6 := fget_lt _ _ _
      have h2 : 2 ^ n < 2 ^ 6 := Nat.pow_lt_pow_right (by omega) (by omega)
      exact Nat.xor_lt_two_pow h1 h2
    set v := colAt C n ^^^ 2 ^ n with hvdef
    have hS' : ∀ a, (S a ∨ a = v) → a < 64 := by
      rintro a (h | rfl)
      · exact hS a h
      · exact hv
    have epred : (fun a => S a ∨ ∃ j < n + 1, a = colAt C j ^^^ 2 ^ j) =
        fun a => (S a ∨ a = v) ∨ ∃ j < n, a = colAt C j ^^^ 2 ^ j := by
      funext a
      apply propext
      constructor
      · rintro (h | ⟨j, hj, rfl⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact Or.inr ⟨j, hj, rfl⟩
          · exact Or.inl (Or.inr rfl)
      · rintro ((h | rfl) | ⟨j, hj, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨n, by omega, rfl⟩
        · exact Or.inr ⟨j, by omega, rfl⟩
    rw [epred, dRec_succ]
    obtain ⟨hr1, hr2, hr3⟩ := redF_spec hP hv 6 le_rfl
    set r := redF P v 6 with hrdef
    split
    · rename_i h0
      have hin : InSp S v := by
        rw [h0, Nat.zero_xor] at hr2
        exact (hsp v).1 hr2
      rw [dRec_spec C n (by omega) P (fun a => S a ∨ a = v) hP hS'
        (fun x => by rw [hsp x, InSp.insert_of_mem hin]),
        spanF_congr (fun x => InSp.insert_of_mem hin)]
    · rename_i h0
      have hn' : ¬ InSp S v := by
        intro hin
        apply h0
        have h1 : InSp (PivSet P 6) v := (hsp v).2 hin
        have h2 := hr2.xor h1
        rw [xor_xor_cancel] at h2
        exact piv_zero hP 6 le_rfl r h2 fun t ht hne => hr3 t (by omega) ht hne
      obtain ⟨hl6, hlb, hllt⟩ := lead6_spec r hr1 h0
      set l := lead6 r with hldef
      have hl0 : fget P l 6 = 0 := by
        by_contra hne
        rw [hr3 l (by omega) hl6 hne] at hlb
        exact absurd hlb (by decide)
      have hF := fget_lor_shl hl0 hr1
      have hP' : PivOK (P ||| r <<< (6 * l)) := by
        intro t ht
        rw [hF t]
        split
        · rename_i htl
          subst htl
          exact Or.inr ⟨hlb, hllt⟩
        · exact hP t ht
      have hsp' : ∀ x, InSp (PivSet (P ||| r <<< (6 * l)) 6) x ↔ InSp (fun a => S a ∨ a = v) x := by
        have e1 : ∀ x, InSp (PivSet (P ||| r <<< (6 * l)) 6) x ↔
            InSp (fun a => PivSet P 6 a ∨ a = r) x := by
          intro x
          constructor
          · apply InSp.mono
            rintro a ⟨t, ht, rfl⟩
            rw [hF t]
            split
            · exact InSp.of_mem (Or.inr rfl)
            · exact InSp.of_mem (Or.inl ⟨t, ht, rfl⟩)
          · apply InSp.mono
            rintro a (⟨t, ht, rfl⟩ | rfl)
            · by_cases htl : t = l
              · subst htl
                rw [hl0]
                exact InSp.zero
              · apply InSp.of_mem
                refine ⟨t, ht, ?_⟩
                rw [hF t, if_neg htl]
            · apply InSp.of_mem
              refine ⟨l, hl6, ?_⟩
              rw [hF l, if_pos rfl]
        intro x
        rw [e1, InSp.insert_swap hr2, InSp.insert_iff, InSp.insert_iff, hsp, hsp]
      rw [dRec_spec C n (by omega) _ (fun a => S a ∨ a = v) hP' hS' hsp',
        card_spanF_insert hS hv hn']
      ring

theorem pivOK_zero : PivOK 0 := by
  intro t _
  left
  rw [fget_eq, Nat.zero_shiftRight, Nat.zero_mod]

theorem dickK_eq_dickC {X : ℕ} {L : List ℕ} (hL : ∀ j < 6, L.getD j 0 = colAt X j) :
    dickK X = if dickC L = true then 1 else 0 := by
  have hL' : ∀ j < 6, L.getD j 0 < 64 := fun j hj => by
    rw [hL j hj]
    exact fget_lt _ _ _
  obtain ⟨c, h1, h2⟩ := dickC_spec hL'
  have h3 := dRec_spec X 6 le_rfl 0 (fun _ => False) pivOK_zero (fun _ h => h.elim) (fun x => by
    constructor
    · intro h
      have : x = 0 := by
        apply InSp.empty
        apply InSp.mono _ h
        rintro a ⟨t, _, rfl⟩
        rw [fget_eq, Nat.zero_shiftRight, Nat.zero_mod]
        exact InSp.zero
      rw [this]
      exact InSp.zero
    · intro h
      rw [h.empty]
      exact InSp.zero)
  rw [card_spanF_empty, Nat.mul_one] at h3
  have e : (fun a => False ∨ ∃ j < 6, a = colAt X j ^^^ 2 ^ j) =
      fun a => ∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j := by
    funext a
    apply propext
    simp only [false_or]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by rw [hL j hj]⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by rw [hL j hj]⟩
  rw [e, h2] at h3
  have hc : c = dRec X 6 0 := Nat.pow_right_injective (le_refl 2) h3
  rw [dickK_eq, ← hc, h1]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

@[expose] def packL : List ℕ → ℕ
  | [] => 0
  | c :: cs => c ||| packL cs <<< 6

theorem getD_lt {cs : List ℕ} (h : ∀ x ∈ cs, x < 64) (j : ℕ) : cs.getD j 0 < 64 := by
  induction cs generalizing j with
  | nil => simp
  | cons a cs ih =>
    cases j with
    | zero => simpa using h a (by simp)
    | succ j => simpa using ih (fun x hx => h x (by simp [hx])) j

theorem testBit_packL : ∀ (cs : List ℕ), (∀ x ∈ cs, x < 64) → ∀ p,
    (packL cs).testBit p = (cs.getD (p / 6) 0).testBit (p % 6)
  | [], _, p => by simp [packL]
  | c :: cs, h, p => by
    have hc : c < 2 ^ 6 := h c (by simp)
    have ih := testBit_packL cs (fun x hx => h x (by simp [hx]))
    rw [packL, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hp : p < 6
    · have : ¬ 6 ≤ p := by omega
      simp [this, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega)
        (by omega : 6 ≤ p))), ih]
      obtain ⟨k, hk⟩ : ∃ k, p / 6 = k + 1 := ⟨p / 6 - 1, by omega⟩
      have e1 : (p - 6) / 6 = k := by omega
      have e2 : (p - 6) % 6 = p % 6 := by omega
      rw [hk, e1, e2, List.getD_cons_succ]
      simp [show 6 ≤ p by omega]

theorem colAt_packL {cs : List ℕ} (h : ∀ x ∈ cs, x < 64) (j : ℕ) : colAt (packL cs) j = cs.getD j 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (fget (packL cs) j 6).testBit i = _
  rw [testBit_fget, testBit_packL cs h]
  by_cases hi : i < 6
  · have e1 : (j * 6 + i) / 6 = j := by omega
    have e2 : (j * 6 + i) % 6 = i := by omega
    simp [hi, e1, e2]
  · have hlt : cs.getD j 0 < 2 ^ 6 := getD_lt h j
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega)
      (by omega : 6 ≤ i)))]
    simp [hi]

theorem packL_append (c : ℕ) : ∀ cs : List ℕ, packL (cs ++ [c]) = packL cs ||| c <<< (6 * cs.length)
  | [] => by simp [packL]
  | a :: cs => by
    rw [List.cons_append, packL, packL, packL_append c cs, List.length_cons]
    apply Nat.eq_of_testBit_eq
    intro p
    simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases h1 : 6 ≤ p
    · by_cases h2 : 6 * cs.length ≤ p - 6
      · have h3 : 6 * (cs.length + 1) ≤ p := by omega
        have e : p - 6 - 6 * cs.length = p - 6 * (cs.length + 1) := by omega
        simp [h1, h2, h3, e, Bool.or_assoc]
      · have h3 : ¬ 6 * (cs.length + 1) ≤ p := by omega
        simp [h1, h2, h3]
    · have h3 : ¬ 6 * (cs.length + 1) ≤ p := by omega
      simp [h1, h3]

theorem testBit_toNat_shl (b : Bool) (c p : ℕ) :
    (b.toNat <<< c).testBit p = (b && decide (c = p)) := by
  cases b
  · simp
  · change (1 <<< c).testBit p = _
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp

theorem testBit_toNat (b : Bool) (k : ℕ) : b.toNat.testBit k = (b && decide (k = 0)) := by
  cases b
  · simp
  · cases k with
    | zero => rfl
    | succ k => simp [Nat.testBit_succ]

theorem qK_eq (e x : ℕ) : qK e x = (e.testBit x).toNat := bitN_eq e x

theorem bfK_eq (e x y : ℕ) :
    bfK e x y = (e.testBit (x ^^^ y) ^^ e.testBit x ^^ e.testBit y).toNat := by
  change Nat.xor (Nat.xor (qK e (Nat.xor x y)) (qK e x)) (qK e y) = _
  rw [qK_eq, qK_eq, qK_eq, xor_toNat, xor_toNat]
  rfl

theorem testBit_qMask (e p : ℕ) : (qMask e).testBit p = (decide (p < 64) && e.testBit p) := by
  rw [Bool.eq_iff_iff]
  unfold qMask
  rw [testBit_orN_iff]
  simp only [qK_eq]
  change (∃ i < 64, (( e.testBit i).toNat <<< i).testBit p = true) ↔ _
  simp only [testBit_toNat_shl, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, h, rfl⟩
    exact ⟨hi, h⟩
  · rintro ⟨hp, h⟩
    exact ⟨p, hp, h, rfl⟩

theorem testBit_bfTab (e x c : ℕ) (hx : x < 64) (hc : c < 64) :
    (fget (bfTab e) x 64).testBit c = (e.testBit (x ^^^ c) ^^ e.testBit x ^^ e.testBit c) := by
  rw [testBit_fget, Bool.eq_iff_iff]
  simp only [hc, decide_true, Bool.true_and]
  unfold bfTab
  rw [testBit_orN_iff]
  change (∃ i < 64, ((orN 64 fun c => bfK e i c <<< c) <<< (64 * i)).testBit (x * 64 + c) = true) ↔ _
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, testBit_orN_iff,
    bfK_eq, testBit_toNat]
  constructor
  · rintro ⟨i, hi, hle, j, hj, hle2, h, hz⟩
    rw [show i = x by omega, show j = c by omega] at h
    exact h
  · intro h
    exact ⟨x, hx, by omega, c, hc, by omega, h, by omega⟩

@[expose] noncomputable def candR (e BT QM C k n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (nIf(Nat.beq (qK e (pw2 k)) (nat_lit 1), QM, Nat.xor QM (maskN (nat_lit 64))))
    (fun i ih => strictN ih fun m => Nat.land m
      (nIf(Nat.beq (bfK e (pw2 i) (pw2 k)) (nat_lit 1), fget BT (colAt C i) (nat_lit 64),
        Nat.xor (fget BT (colAt C i) (nat_lit 64)) (maskN (nat_lit 64)))))
    n

theorem candK_eq (e BT QM C k : Nat) : candK e BT QM C k = candR e BT QM C k k := rfl

theorem testBit_mask64 (p : ℕ) : (maskN 64).testBit p = decide (p < 64) := by
  rw [maskN_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_land (a b i : ℕ) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i

theorem testBit_nxor (a b i : ℕ) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) :=
  Nat.testBit_xor a b i

theorem candR_spec {q : ℕ → Bool} {Q : ℕ} (hq : QBind q Q) {cs : List ℕ} (hk : cs.length < 6)
    (hcs : ∀ x ∈ cs, x < 64) : ∀ n ≤ cs.length,
    candR Q (bfTab Q) (qMask Q) (packL cs) cs.length n < 2 ^ 64 ∧
      ∀ c < 64, (candR Q (bfTab Q) (qMask Q) (packL cs) cs.length n).testBit c =
        (q c == q (2 ^ cs.length) && (List.range n).all fun i =>
          bfG q (cs.getD i 0) c == bfG q (2 ^ i) (2 ^ cs.length))
  | 0, _ => by
    have hk2 : 2 ^ cs.length < 64 := by
      have := Nat.pow_lt_pow_right (a := 2) (by omega) hk
      simpa using this
    have hQM : qMask Q < 2 ^ 64 := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rw [testBit_qMask]
      simp
      omega
    change nIf(Nat.beq (qK Q (pw2 cs.length)) (nat_lit 1), qMask Q,
      Nat.xor (qMask Q) (maskN (nat_lit 64))) < _ ∧ ∀ c < 64, (nIf(Nat.beq (qK Q (pw2 cs.length))
        (nat_lit 1), qMask Q, Nat.xor (qMask Q) (maskN (nat_lit 64)))).testBit c = _
    rw [nIf_eq, qK_eq, beq_toNat_one, pw2_eq, ← hq _ hk2]
    refine ⟨?_, fun c hc => ?_⟩
    · split
      · exact hQM
      · exact Nat.xor_lt_two_pow hQM (by rw [maskN_eq]; omega)
    · split
      · rename_i h
        rw [testBit_qMask, ← hq c hc, h]
        simp [hc]
      · rename_i h
        change (qMask Q ^^^ maskN 64).testBit c = _
        rw [Nat.testBit_xor, testBit_qMask, testBit_mask64, ← hq c hc]
        simp only [Bool.not_eq_true] at h
        rw [h]
        cases q c <;> simp [hc]
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := candR_spec hq hk hcs n (by omega)
    have hx : cs.getD n 0 < 64 := getD_lt hcs n
    have hn2 : 2 ^ n < 64 := by
      have := Nat.pow_lt_pow_right (a := 2) (by omega) (show n < 6 by omega)
      simpa using this
    have hk2 : 2 ^ cs.length < 64 := by
      have := Nat.pow_lt_pow_right (a := 2) (by omega) hk
      simpa using this
    have hb : bfK Q (2 ^ n) (2 ^ cs.length) = (bfG q (2 ^ n) (2 ^ cs.length)).toNat := by
      rw [bfK_eq, bfG, hq _ (by
        have := Nat.xor_lt_two_pow (n := 6) (x := 2 ^ n) (y := 2 ^ cs.length) hn2 hk2
        simpa using this), hq _ hn2, hq _ hk2]
    change strictN (candR Q (bfTab Q) (qMask Q) (packL cs) cs.length n) (fun m => Nat.land m
      (nIf(Nat.beq (bfK Q (pw2 n) (pw2 cs.length)) (nat_lit 1), fget (bfTab Q) (colAt (packL cs) n)
        (nat_lit 64), Nat.xor (fget (bfTab Q) (colAt (packL cs) n) (nat_lit 64))
          (maskN (nat_lit 64))))) < _ ∧ ∀ c < 64, (strictN (candR Q (bfTab Q) (qMask Q) (packL cs)
            cs.length n) (fun m => Nat.land m (nIf(Nat.beq (bfK Q (pw2 n) (pw2 cs.length))
              (nat_lit 1), fget (bfTab Q) (colAt (packL cs) n) (nat_lit 64),
                Nat.xor (fget (bfTab Q) (colAt (packL cs) n) (nat_lit 64))
                  (maskN (nat_lit 64)))))).testBit c = _
    rw [strictN_eq]
    beta_reduce
    rw [nIf_eq, pw2_eq, pw2_eq, hb, beq_toNat_one, colAt_packL hcs]
    refine ⟨Nat.lt_of_le_of_lt Nat.and_le_left h1, fun c hc => ?_⟩
    rw [testBit_land, h2 c hc, List.range_succ, List.all_append]
    have hbt : (fget (bfTab Q) (cs.getD n 0) 64).testBit c = bfG q (cs.getD n 0) c := by
      rw [testBit_bfTab Q _ c hx hc, bfG, hq _ (by
        have := Nat.xor_lt_two_pow (n := 6) (x := cs.getD n 0) (y := c) hx hc
        simpa using this), hq _ hx, hq _ hc]
    split
    · rename_i h
      rw [hbt, List.all_cons, List.all_nil, Bool.and_true, h]
      generalize bfG q (cs.getD n 0) c = b
      cases b <;> simp [Bool.and_assoc]
    · rename_i h
      rw [testBit_nxor, hbt, testBit_mask64, List.all_cons, List.all_nil, Bool.and_true]
      simp only [Bool.not_eq_true] at h
      rw [h]
      generalize bfG q (cs.getD n 0) c = b
      cases b <;> simp [hc, Bool.and_assoc]

theorem lowBit_spec : ∀ w : Nat, w ≠ 0 → ∃ k, w &&& (w ^^^ (w - 1)) = 2 ^ k ∧
    w.testBit k = true ∧ ∀ i < k, w.testBit i = false
  | w, hw => by
    rcases Nat.mod_two_eq_zero_or_one w with he | ho
    · have hw2 : w / 2 ≠ 0 := by omega
      obtain ⟨k, hk1, hk2, hk3⟩ := lowBit_spec (w / 2) hw2
      refine ⟨k + 1, ?_, by rw [Nat.testBit_succ]; exact hk2, fun i hi => ?_⟩
      · apply Nat.eq_of_testBit_eq
        intro j
        cases j with
        | zero =>
          rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_zero w]
          simp [he]
        | succ j =>
          have e1 : (w - 1) / 2 = w / 2 - 1 := by omega
          have h2 := congrArg (fun t => t.testBit j) hk1
          simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow] at h2
          rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_succ w,
            Nat.testBit_succ (w - 1), e1, h2]
          simp
      · cases i with
        | zero => simp [Nat.testBit_zero, he]
        | succ i =>
          rw [Nat.testBit_succ]
          exact hk3 i (by omega)
    · refine ⟨0, ?_, by simp [Nat.testBit_zero, ho], fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      apply Nat.eq_of_testBit_eq
      intro j
      cases j with
      | zero =>
        rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_zero w,
          Nat.testBit_zero (w - 1)]
        have : (w - 1) % 2 = 0 := by omega
        simp [ho, this]
      | succ j =>
        rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_succ w,
          Nat.testBit_succ (w - 1)]
        have : (w - 1) / 2 = w / 2 := by omega
        rw [this]
        simp

theorem pop64_pow : ∀ k < 64, CFSG.KC.Local.pop64 (2 ^ k - 1) = k := by decide

@[expose] noncomputable def wSumF (g : Nat → Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih w s => nIf(Nat.beq w (nat_lit 0), s,
      (fun low => strictN ((fun c s => Nat.add s (g c))
          (Nat.add (nat_lit 0) (CFSG.KC.Local.pop64 (Nat.sub low (nat_lit 1)))) s)
        (fun s2 => ih (Nat.xor w low) s2))
      (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1)))))) n

theorem wSumF_spec (g : Nat → Nat) : ∀ n w s, w < 2 ^ 64 → (∀ i < 64 - n, w.testBit i = false) →
    wSumF g n w s = s + ∑ c ∈ Finset.range 64, if w.testBit c = true then g c else 0
  | n, w, s, hw, hlow => by
    by_cases hw0 : w = 0
    · subst hw0
      have : wSumF g n 0 s = s := by cases n <;> rfl
      rw [this]
      simp
    cases n with
    | zero =>
      exfalso
      apply hw0
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.zero_testBit]
      rcases Nat.lt_or_ge i 64 with hi | hi
      · exact hlow i (by omega)
      · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hi))
    | succ n =>
      obtain ⟨k0, hl, hk0, hlt⟩ := lowBit_spec w hw0
      have hk064 : k0 < 64 := by
        by_contra hc
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega)
          (by omega)))] at hk0
        exact absurd hk0 (by decide)
      have hk0n : 64 - (n + 1) ≤ k0 := by
        by_contra hc
        rw [hlow k0 (by omega)] at hk0
        exact absurd hk0 (by decide)
      have hstep : wSumF g (n + 1) w s = wSumF g n (w ^^^ 2 ^ k0) (s + g k0) := by
        have h1 : wSumF g (n + 1) w s = Bool.rec (motive := fun _ => Nat)
            ((fun low => strictN ((fun c s => Nat.add s (g c))
                (Nat.add 0 (CFSG.KC.Local.pop64 (Nat.sub low 1))) s)
              (fun s2 => wSumF g n (Nat.xor w low) s2))
              (Nat.land w (Nat.xor w (Nat.sub w 1)))) s (Nat.beq w 0) := rfl
        have hb : Nat.beq w 0 = false := by
          cases h : Nat.beq w 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) hw0
        rw [h1, hb]
        change strictN (s + g (0 + CFSG.KC.Local.pop64 ((w &&& (w ^^^ (w - 1))) - 1)))
          (fun s2 => wSumF g n (w ^^^ (w &&& (w ^^^ (w - 1)))) s2) = _
        rw [strictN_eq, hl, pop64_pow k0 hk064, Nat.zero_add]
      have ih := wSumF_spec g n (w ^^^ 2 ^ k0) (s + g k0)
        (Nat.xor_lt_two_pow hw (Nat.pow_lt_pow_right (by omega) hk064)) (by
          intro i hi
          rw [Nat.testBit_xor, Nat.testBit_two_pow]
          rcases Nat.lt_or_ge i k0 with h1 | h1
          · rw [hlt i h1]
            simp
            omega
          · have : i = k0 := by omega
            simp [this, hk0])
      have hsplit : ∀ c ∈ Finset.range 64, (if w.testBit c = true then g c else 0) =
          (if (w ^^^ 2 ^ k0).testBit c = true then g c else 0) + (if k0 = c then g k0 else 0) := by
        intro c _
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        by_cases hc : k0 = c
        · subst hc
          simp [hk0]
        · simp [hc]
      rw [hstep, ih, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq,
        if_pos (Finset.mem_range.2 hk064)]
      omega

theorem wordFold_sum (g : Nat → Nat) (w s : Nat) (hw : w < 2 ^ 64) :
    CFSG.KC.Local.wordFold (fun c s => Nat.add s (g c)) (nat_lit 0) w s =
      s + ∑ c ∈ Finset.range 64, if w.testBit c = true then g c else 0 :=
  wSumF_spec g 64 w s hw (fun i hi => absurd hi (by omega))

theorem sum_flatMap_map {α β : Type} (l : List α) (g : α → List β) (f : β → ℕ) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_filter_range (m : ℕ) (p : ℕ → Bool) (h : ℕ → ℕ) :
    (((List.range m).filter p).map h).sum = ∑ c ∈ Finset.range m, if p c = true then h c else 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    cases hp : p m <;> simp [hp]

theorem walkK_spec {q : ℕ → Bool} {Q : ℕ} (hq : QBind q Q) (f : ℕ → ℕ) : ∀ n ≤ 5,
    ∀ cs : List ℕ, cs.length + n = 6 → (∀ x ∈ cs, x < 64) →
    walkK Q (bfTab Q) (qMask Q) f n (packL cs) = ((oColsAuxG q n cs).map fun C => f (packL C)).sum
  | 0, _, cs, _, _ => by
    change f (packL cs) = _
    simp [oColsAuxG]
  | n + 1, hn, cs, hl, hcs => by
    have hk : 5 - n = cs.length := by omega
    change CFSG.KC.Local.wordFold (fun c s => Nat.add s (walkK Q (bfTab Q) (qMask Q) f n
      (packL cs ||| c <<< (6 * (5 - n))))) (nat_lit 0) (candK Q (bfTab Q) (qMask Q) (packL cs) (5 - n))
        (nat_lit 0) = _
    rw [hk, candK_eq]
    obtain ⟨hlt, hbits⟩ := candR_spec hq (by omega) hcs cs.length le_rfl
    rw [wordFold_sum _ _ _ hlt, Nat.zero_add, oColsAuxG, sum_flatMap_map, extendColsG,
      sum_filter_range]
    apply Finset.sum_congr rfl
    intro c hc
    have hc64 : c < 64 := Finset.mem_range.1 hc
    rw [hbits c hc64]
    split
    · rw [← packL_append, walkK_spec hq f n (by omega) (cs ++ [c]) (by simp; omega)
        (fun x hx => by
          rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hcs x hx
          · exact hc64)]
    · rfl

theorem walkFrom_eq {q : ℕ → Bool} {Q : ℕ} (hq : QBind q Q) (f : ℕ → ℕ) {c : ℕ} (hc : c < 64) :
    walkFrom Q f c = if (q c == q 1) = true then ((oColsAuxG q 5 [c]).map fun C => f (packL C)).sum
      else 0 := by
  change strictN (bfTab Q) (fun BT => strictN (qMask Q) fun QM =>
    nIf(Nat.beq (bitN (candK Q BT QM (nat_lit 0) (nat_lit 0)) c) (nat_lit 1),
      walkK Q BT QM f (nat_lit 5) c, nat_lit 0)) = _
  rw [strictN_eq, strictN_eq, nIf_eq, beq_bitN]
  have hp : packL ([] : List ℕ) = 0 := rfl
  obtain ⟨-, hbits⟩ := candR_spec hq (cs := []) (by simp) (by simp) 0 le_rfl
  have hb := hbits c hc
  rw [hp] at hb
  change (candK Q (bfTab Q) (qMask Q) 0 0).testBit c = _ at hb
  have hc1 : packL [c] = c := by simp [packL]
  have hw := walkK_spec hq f 5 le_rfl [c] rfl (by simpa using hc)
  rw [hc1] at hw
  rw [hb, hw]
  simp

theorem sum_walkFrom {q : ℕ → Bool} {Q : ℕ} (hq : QBind q Q) (f : ℕ → ℕ) :
    ∑ c ∈ Finset.range 64, walkFrom Q f c = ((oColsG q).map fun C => f (packL C)).sum := by
  rw [oColsG, oColsAuxG, sum_flatMap_map, extendColsG, sum_filter_range]
  apply Finset.sum_congr rfl
  intro c hc
  rw [walkFrom_eq hq f (Finset.mem_range.1 hc)]
  simp

theorem mem_oColsAuxG {q : ℕ → Bool} : ∀ (n : ℕ) (cs C : List ℕ), C ∈ oColsAuxG q n cs →
    (∀ x ∈ cs, x < 64) → C.length = cs.length + n ∧ ∀ x ∈ C, x < 64
  | 0, cs, C, hC, hcs => by
    simp only [oColsAuxG, List.mem_singleton] at hC
    subst hC
    exact ⟨rfl, hcs⟩
  | n + 1, cs, C, hC, hcs => by
    simp only [oColsAuxG, List.mem_flatMap] at hC
    obtain ⟨c, hc, hC⟩ := hC
    have hc64 : c < 64 := by
      simp only [extendColsG, List.mem_filter, List.mem_range] at hc
      exact hc.1
    obtain ⟨h1, h2⟩ := mem_oColsAuxG n (cs ++ [c]) C hC (fun x hx => by
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hcs x hx
      · exact hc64)
    refine ⟨by rw [h1]; simp; omega, h2⟩

theorem colsActK_eq {X : ℕ} {C : List ℕ} (hC : ∀ d < 6, colAt X d = C.getD d 0) (z : ℕ) :
    colsActK X z = colsAct C z := by
  have : ∀ n ≤ 6, xorN n (fun d => nIf(Nat.beq (bitN z d) (nat_lit 1), colAt X d, nat_lit 0)) =
      colsActAux C z n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.xor (nIf(Nat.beq (bitN z n) (nat_lit 1), colAt X n, nat_lit 0)) (xorN n _) = _
      rw [ih (by omega), colsActAux, nIf_eq, beq_bitN, hC n (by omega)]
      exact Nat.xor_comm _ _
  exact this 6 le_rfl

theorem fixK_eq {X : ℕ} {C : List ℕ} (hC : ∀ d < 6, colAt X d = C.getD d 0) :
    fixK X = fixCount C := by
  change sumN 64 (fun z => nIf(Nat.beq (colsActK X z) z, nat_lit 1, nat_lit 0)) = _
  rw [sumN_ind, fixCount]
  congr 2
  funext z
  rw [colsActK_eq hC]
  rfl

theorem packL_id : packL [1, 2, 4, 8, 16, 32] = 34630287489 := by decide

theorem all_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem involK_eq {C : List ℕ} (hl : C.length = 6) (hc : ∀ x ∈ C, x < 64) :
    involK (packL C) = isInvol C := by
  have hC : ∀ d < 6, colAt (packL C) d = C.getD d 0 := fun d _ => colAt_packL hc d
  change andB (allN 6 fun j => Nat.beq (colsActK (packL C) (colAt (packL C) j)) (pw2 j))
    (notB (Nat.beq (packL C) 34630287489)) = _
  rw [andB_eq, notB_eq, allN_eq, isInvol]
  congr 1
  · apply all_congr_mem
    intro j hj
    rw [colsActK_eq hC, hC j (List.mem_range.1 hj), pw2_eq]
    rfl
  · have hr : (List.range 6).map (2 ^ ·) = [1, 2, 4, 8, 16, 32] := by decide
    rw [hr, ← packL_id]
    have hid : ∀ x ∈ [1, 2, 4, 8, 16, 32], x < 64 := by decide
    congr 1
    change (packL C == packL [1, 2, 4, 8, 16, 32]) = (C == [1, 2, 4, 8, 16, 32])
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    constructor
    · intro h
      apply List.ext_getElem (by rw [hl]; rfl)
      intro j h1 h2
      have := congrArg (colAt · j) h
      simp only [colAt_packL hc, colAt_packL hid] at this
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
        List.getElem?_eq_getElem h2] at this
      simpa using this
    · rintro rfl
      rfl

theorem leaf_ok {C : List ℕ} (hl : C.length = 6) (hc : ∀ x ∈ C, x < 64)
    (h : invBadK (packL C) = 0) : (dickC C || !isInvol C || fixCount C == 16) = true := by
  have hC : ∀ d < 6, colAt (packL C) d = C.getD d 0 := fun d _ => colAt_packL hc d
  have hd := dickK_eq_dickC (X := packL C) (L := C) fun j hj => (hC j hj).symm
  change nIf(Nat.beq (dickK (packL C)) (nat_lit 1), nat_lit 0,
    nIf(involK (packL C), nIf(Nat.beq (fixK (packL C)) (nat_lit 16), nat_lit 0, nat_lit 1),
      nat_lit 0)) = 0 at h
  rw [hd, involK_eq hl hc, fixK_eq hC, nIf_eq, nIf_eq, nIf_eq] at h
  cases hdc : dickC C
  · cases hi : isInvol C
    · simp
    · rw [hdc, hi] at h
      simp only [if_true, Bool.false_eq_true, if_false] at h
      have : Nat.beq (fixCount C) 16 = true := by
        by_contra hne
        rw [if_neg hne] at h
        exact absurd h (by decide)
      simp [Nat.eq_of_beq_eq_true this]
  · simp

theorem sum_getD (L : List ℕ) : ∀ n, L.length ≤ n → ∑ c ∈ Finset.range n, L.getD c 0 = L.sum := by
  induction L with
  | nil => intro n _; simp
  | cons a L ih =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
    rw [ih m (by simp at hn; omega), Nat.add_comm]

theorem sum_map_one {α : Type} (l : List α) : (l.map fun _ => (1 : ℕ)).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.add_comm]

theorem oCount_eq_proved {q : ℕ → Bool} {Q : Nat} {L : List ℕ} (hq : QBind q Q)
    (h : ∀ c < 64, walkFrom Q (fun _ => 1) c = L.getD c 0) (hl : L.length ≤ 64) :
    (oColsG q).length = L.sum := by
  have hs := sum_walkFrom hq (fun _ => 1)
  rw [Finset.sum_congr rfl (fun c hc => h c (Finset.mem_range.1 hc)), sum_getD L 64 hl] at hs
  rw [hs, sum_map_one]

theorem inv_sound_proved {q : ℕ → Bool} {Q : Nat} (hq : QBind q Q)
    (h : ∀ c < 64, walkFrom Q invBadK c = 0) : invCheckG q = true := by
  have hs := sum_walkFrom hq invBadK
  rw [Finset.sum_eq_zero (fun c hc => h c (Finset.mem_range.1 hc))] at hs
  rw [invCheckG, List.all_eq_true]
  intro C hC
  obtain ⟨hl, hc⟩ := mem_oColsAuxG 6 [] C hC (by simp)
  refine leaf_ok (by simpa using hl) hc ?_
  exact (List.sum_eq_zero_iff.1 hs.symm) _ (List.mem_map_of_mem hC)

end CFSG.KC.O8.OrthPf

end
