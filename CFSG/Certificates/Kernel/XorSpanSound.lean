module

public import Certificates.Data.Kernel.XorSpan
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Mathlib.Order.WellFounded
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.XorSpan

open CFSG.KC.Enum

@[expose] def xsel (r : Nat → Nat) (c : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => xsel r c n ^^^ (if c n then r n else 0)

theorem xsel_succ (r : Nat → Nat) (c : Nat → Bool) (n : Nat) :
    xsel r c (n + 1) = xsel r c n ^^^ (if c n then r n else 0) := rfl

theorem xsel_congr {r r' : Nat → Nat} {c c' : Nat → Bool} {n : Nat}
    (hr : ∀ k < n, c k = true → r k = r' k) (hc : ∀ k < n, c k = c' k) :
    xsel r c n = xsel r' c' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xsel_succ, xsel_succ, ih (fun k hk => hr k (by omega)) (fun k hk => hc k (by omega)),
      ← hc n (by omega)]
    by_cases h : c n = true
    · simp only [h, ↓reduceIte, hr n (by omega) h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem xsel_lt {r : Nat → Nat} {c : Nat → Bool} {q : Nat} :
    ∀ {n : Nat}, (∀ k < n, c k = true → r k < 2 ^ q) → xsel r c n < 2 ^ q
  | 0, _ => Nat.two_pow_pos q
  | n + 1, h => by
    rw [xsel_succ]
    refine Nat.xor_lt_two_pow (xsel_lt fun k hk => h k (by omega)) ?_
    by_cases hc : c n = true
    · simp only [hc, ↓reduceIte]
      exact h n (by omega) hc
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact Nat.two_pow_pos q

theorem xsel_xor (r : Nat → Nat) (c c' : Nat → Bool) :
    ∀ n, xsel r c n ^^^ xsel r c' n = xsel r (fun k => c k ^^ c' k) n
  | 0 => Nat.xor_self 0
  | n + 1 => by
    rw [xsel_succ, xsel_succ, xsel_succ, ← xsel_xor r c c' n]
    have e : ∀ a b x y : Nat, a ^^^ x ^^^ (b ^^^ y) = a ^^^ b ^^^ (x ^^^ y) := by
      intro a b x y
      rw [Nat.xor_assoc, Nat.xor_assoc, ← Nat.xor_assoc x, Nat.xor_comm x b, Nat.xor_assoc b]
    rw [e]
    congr 1
    cases c n <;> cases c' n <;> simp

theorem eq_of_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem xsel_false (r : Nat → Nat) : ∀ n, xsel r (fun _ => false) n = 0
  | 0 => rfl
  | n + 1 => by
    rw [xsel_succ, xsel_false r n]
    exact Nat.xor_self 0

@[expose] def Lin (w : Nat) (f : Nat → Nat) : Prop :=
  ∀ a < 2 ^ w, ∀ b < 2 ^ w, f (a ^^^ b) = f a ^^^ f b

theorem Lin.map_zero {w : Nat} {f : Nat → Nat} (hf : Lin w f) : f 0 = 0 := by
  have := hf 0 (Nat.two_pow_pos w) 0 (Nat.two_pow_pos w)
  rw [Nat.xor_self] at this
  rw [this, Nat.xor_self]

theorem Lin.map_xsel {w : Nat} {f : Nat → Nat} (hf : Lin w f) {r : Nat → Nat} {c : Nat → Bool} :
    ∀ {n : Nat}, (∀ k < n, r k < 2 ^ w) → f (xsel r c n) = xsel (fun k => f (r k)) c n
  | 0, _ => hf.map_zero
  | n + 1, h => by
    rw [xsel_succ, xsel_succ, hf _ (xsel_lt fun k hk _ => h k (by omega)) _ (by
      split
      · exact h n (by omega)
      · exact Nat.two_pow_pos w), Lin.map_xsel hf fun k hk => h k (by omega)]
    congr 1
    split
    · rfl
    · exact hf.map_zero

theorem Lin.inj {w : Nat} {f : Nat → Nat} (hf : Lin w f) (h0 : ∀ a < 2 ^ w, f a = 0 → a = 0)
    {a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (h : f a = f b) : a = b := by
  have := h0 _ (Nat.xor_lt_two_pow ha hb) (by rw [hf a ha b hb, h, Nat.xor_self])
  exact eq_of_xor_eq_zero this

theorem testBit_xsel_pow (c : Nat → Bool) (n p : Nat) :
    (xsel (fun k => 2 ^ k) c n).testBit p = (decide (p < n) && c p) := by
  induction n with
  | zero => simp [xsel]
  | succ n ih =>
    rw [xsel_succ, Nat.testBit_xor, ih]
    by_cases hc : c n = true
    · simp only [hc, ↓reduceIte]
      rw [Nat.testBit_two_pow]
      by_cases hp : p = n
      · subst hp
        simp [hc]
      · have : ¬ n = p := fun e => hp e.symm
        simp only [this, decide_false, Bool.xor_false]
        by_cases hp' : p < n
        · simp [hp', show p < n + 1 by omega]
        · simp [hp', show ¬ p < n + 1 by omega]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.zero_testBit, Bool.xor_false]
      by_cases hp : p = n
      · subst hp
        simp [hc]
      · by_cases hp' : p < n
        · simp [hp', show p < n + 1 by omega]
        · simp [hp', show ¬ p < n + 1 by omega]

theorem eq_of_testBit_lt {s s' n : Nat} (hs : s < 2 ^ n) (hs' : s' < 2 ^ n)
    (h : ∀ k < n, s.testBit k = s'.testBit k) : s = s' := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · exact h k hk
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hs' (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem testBit_fld (x o w i : Nat) :
    (Nat.land (Nat.shiftRight x o) (2 ^ w - 1)).testBit i =
      (decide (i < w) && x.testBit (o + i)) := by
  change (x >>> o &&& 2 ^ w - 1).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem fld_lt (x o w : Nat) : Nat.land (Nat.shiftRight x o) (2 ^ w - 1) < 2 ^ w := by
  change x >>> o &&& 2 ^ w - 1 < 2 ^ w
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem bit_eq_one_iff (v p : Nat) : Nat.beq fld(v, p, nat_lit 1) (nat_lit 1) = v.testBit p := by
  have e : Nat.land (Nat.shiftRight v p) (nat_lit 1) = (v >>> p) % 2 := Nat.and_one_is_mod _
  rw [e, Nat.testBit, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ p) with h | h
  · rw [h, Nat.one_and_eq_mod_two, h]
    rfl
  · rw [h, Nat.one_and_eq_mod_two, h]
    rfl

theorem bit_eq_zero_iff (v p : Nat) :
    Nat.beq fld(v, p, nat_lit 1) (nat_lit 0) = !v.testBit p := by
  have e : Nat.land (Nat.shiftRight v p) (nat_lit 1) = (v >>> p) % 2 := Nat.and_one_is_mod _
  rw [e, Nat.testBit, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ p) with h | h
  · rw [h, Nat.one_and_eq_mod_two, h]
    rfl
  · rw [h, Nat.one_and_eq_mod_two, h]
    rfl

@[expose] noncomputable def spanOf (d w m K s : Nat) : Nat := xsel (row w m K) s.testBit d

@[expose] noncomputable def spanList (d w m K : Nat) : List Nat :=
  (List.range (2 ^ d)).map (spanOf d w m K)

@[expose] noncomputable def spanTab (d w m K : Nat) : Array Nat :=
  ((spanList d w m K).mergeSort (· ≤ ·)).toArray

structure Rref (d w m dw K : Nat) : Prop where
  top : K < 2 ^ (dw + 8 * d)
  piv_bit : ∀ k < d, (row w m K k).testBit (piv dw K k) = true
  row_lt : ∀ k < d, row w m K k < 2 ^ (piv dw K k + 1)
  off : ∀ k < d, ∀ l < d, l ≠ k → (row w m K l).testBit (piv dw K k) = false
  mono : ∀ k, k + 1 < d → piv dw K k < piv dw K (k + 1)

theorem rref_of {d w m dw K : Nat} (h : rrefK d w m dw K = true) : Rref d w m dw K := by
  unfold rrefK at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hk := CFSG.KS.allN_spec h2
  have hk' : ∀ k < d, _ := fun k hk0 => by
    have := hk k hk0
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at this
    exact (CFSG.KS.bAnd_iff _ _).1 this
  refine ⟨?_, fun k hk0 => ?_, fun k hk0 => ?_, fun k hk0 l hl hlk => ?_, fun k hk1 => ?_⟩
  · have e : K >>> (dw + (d <<< 3)) = 0 := Nat.eq_of_beq_eq_true h1
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at e
    rw [Nat.div_eq_zero_iff] at e
    rcases e with e | e
    · exact absurd e (Nat.ne_of_gt (Nat.two_pow_pos _))
    · rw [show 8 * d = d * 2 ^ 3 by omega]
      exact e
  · have := (hk' k hk0).1
    rwa [bit_eq_one_iff] at this
  · have := ((CFSG.KS.bAnd_iff _ _).1 (hk' k hk0).2).1
    have e : row w m K k >>> (piv dw K k + 1) = 0 := Nat.eq_of_beq_eq_true this
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at e
    rcases e with e | e
    · exact absurd e (Nat.ne_of_gt (Nat.two_pow_pos _))
    · exact e
  · have h3 := ((CFSG.KS.bAnd_iff _ _).1 ((CFSG.KS.bAnd_iff _ _).1 (hk' k hk0).2).2).1
    have := CFSG.KS.allN_spec h3 l hl
    rw [CFSG.KS.Raw.Orb.bIf_eq] at this
    have hne : Nat.beq l k = false :=
      Bool.eq_false_iff.mpr fun e => hlk (Nat.eq_of_beq_eq_true e)
    rw [hne] at this
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [bit_eq_zero_iff] at this
    simpa using this
  · have h3 := ((CFSG.KS.bAnd_iff _ _).1 ((CFSG.KS.bAnd_iff _ _).1 (hk' k (by omega)).2).2).2
    rw [CFSG.KS.Raw.Orb.bIf_eq] at h3
    have hlt : Nat.blt (Nat.succ k) d = true := Nat.blt_eq.mpr hk1
    rw [hlt] at h3
    simp only [↓reduceIte] at h3
    exact Nat.blt_eq.mp h3

variable {d w m dw K : Nat}

theorem Rref.piv_le (R : Rref d w m dw K) {k l : Nat} (hkl : k ≤ l) (hl : l < d) :
    piv dw K k ≤ piv dw K l := by
  induction l with
  | zero => rw [Nat.le_zero.mp hkl]
  | succ l ih =>
    rcases Nat.lt_or_eq_of_le hkl with h | h
    · exact Nat.le_of_lt (lt_of_le_of_lt (ih (by omega) (by omega)) (R.mono l hl))
    · rw [h]

theorem Rref.piv_lt (R : Rref d w m dw K) {k l : Nat} (hkl : k < l) (hl : l < d) :
    piv dw K k < piv dw K l :=
  lt_of_le_of_lt (R.piv_le (k := k) (l := l - 1) (by omega) (by omega))
    (by have := R.mono (l - 1) (by omega); rwa [Nat.sub_add_cancel (by omega)] at this)

theorem testBit_xsel_piv (R : Rref d w m dw K) (c : Nat → Bool) {k : Nat} (hk : k < d) :
    ∀ n ≤ d, (xsel (row w m K) c n).testBit (piv dw K k) = (decide (k < n) && c k)
  | 0, _ => by simp [xsel]
  | n + 1, hn => by
    rw [xsel_succ, Nat.testBit_xor, testBit_xsel_piv R c hk n (by omega)]
    by_cases hkn : k = n
    · subst hkn
      by_cases hc : c k = true
      · simp [hc, R.piv_bit k hk]
      · simp [hc]
    · have hb : (if c n = true then row w m K n else 0).testBit (piv dw K k) = false := by
        split
        · exact R.off k hk n (by omega) (fun e => hkn e.symm)
        · exact Nat.zero_testBit _
      rw [hb, Bool.xor_false]
      by_cases hkl : k < n
      · simp [hkl, show k < n + 1 by omega]
      · simp [hkl, show ¬ k < n + 1 by omega]

theorem row_lt (hm : m = 2 ^ w - 1) (k : Nat) : row w m K k < 2 ^ w := by
  unfold row
  rw [hm]
  exact fld_lt _ _ _

theorem spanOf_lt (hm : m = 2 ^ w - 1) (s : Nat) : spanOf d w m K s < 2 ^ w :=
  xsel_lt fun k _ _ => row_lt hm k

theorem spanOf_testBit_piv (R : Rref d w m dw K) {k : Nat} (hk : k < d) (s : Nat) :
    (spanOf d w m K s).testBit (piv dw K k) = s.testBit k := by
  rw [spanOf, testBit_xsel_piv R _ hk d le_rfl]
  simp [hk]

theorem spanOf_inj (R : Rref d w m dw K) {s s' : Nat} (hs : s < 2 ^ d) (hs' : s' < 2 ^ d)
    (h : spanOf d w m K s = spanOf d w m K s') : s = s' :=
  eq_of_testBit_lt hs hs' fun k hk => by
    rw [← spanOf_testBit_piv R hk, ← spanOf_testBit_piv R hk, h]

theorem spanOf_xor (s s' : Nat) :
    spanOf d w m K s ^^^ spanOf d w m K s' = spanOf d w m K (s ^^^ s') := by
  rw [spanOf, spanOf, spanOf, xsel_xor]
  exact xsel_congr (fun _ _ _ => rfl) fun k _ => (Nat.testBit_xor s s' k).symm

theorem spanOf_zero : spanOf d w m K 0 = 0 :=
  (xsel_congr (c' := fun _ => false) (fun _ _ _ => rfl) fun k _ => Nat.zero_testBit k).trans
    (xsel_false _ d)

theorem spanOf_pow {k : Nat} (hk : k < d) : spanOf d w m K (2 ^ k) = row w m K k := by
  rw [spanOf]
  have : ∀ n, xsel (row w m K) (2 ^ k).testBit n = if k < n then row w m K k else 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [xsel_succ, ih, Nat.testBit_two_pow]
      by_cases hkn : k = n
      · subst hkn
        simp
      · by_cases hkl : k < n
        · simp [hkl, show k < n + 1 by omega, hkn]
        · simp [hkl, show ¬ k < n + 1 by omega, hkn]
  rw [this d]
  simp [hk]

theorem red_eq (R : Rref d w m dw K) : ∀ n ≤ d, ∀ v,
    red w m dw K n v = v ^^^ xsel (row w m K) (fun k => v.testBit (piv dw K k)) n
  | 0, _, v => by
    change v = v ^^^ 0
    rw [Nat.xor_zero]
  | n + 1, hn, v => by
    change strictN (xorIf w m dw K n v) (red w m dw K n) = _
    rw [CFSG.KS.Raw.Orb.strictN_eq, red_eq R n (by omega)]
    have hx : xorIf w m dw K n v = v ^^^ (if v.testBit (piv dw K n) then row w m K n else 0) := by
      unfold xorIf
      rw [CFSG.KS.Raw.Orb.nIf_eq, bit_eq_one_iff]
      split
      · rfl
      · rw [Nat.xor_zero]
    have hc : ∀ k < n, (xorIf w m dw K n v).testBit (piv dw K k) = v.testBit (piv dw K k) := by
      intro k hk
      rw [hx, Nat.testBit_xor]
      have : (if v.testBit (piv dw K n) = true then row w m K n else 0).testBit (piv dw K k) =
          false := by
        split
        · exact R.off k (by omega) n (by omega) (by omega)
        · exact Nat.zero_testBit _
      rw [this, Bool.xor_false]
    rw [xsel_congr (c' := fun k => v.testBit (piv dw K k)) (fun _ _ _ => rfl) hc, hx, xsel_succ,
      Nat.xor_assoc]
    congr 1
    exact Nat.xor_comm _ _

theorem inSpan_iff (R : Rref d w m dw K) (v : Nat) :
    inSpan d w m dw K v = true ↔ ∃ s < 2 ^ d, spanOf d w m K s = v := by
  unfold inSpan
  rw [Nat.beq_eq, red_eq R d le_rfl]
  constructor
  · intro h
    have hv : v = xsel (row w m K) (fun k => v.testBit (piv dw K k)) d := eq_of_xor_eq_zero h
    refine ⟨xsel (fun k => 2 ^ k) (fun k => v.testBit (piv dw K k)) d, ?_, ?_⟩
    · exact xsel_lt fun k hk _ => Nat.pow_lt_pow_right (by omega) hk
    · rw [spanOf, hv]
      refine xsel_congr (fun _ _ _ => rfl) fun k hk => ?_
      rw [testBit_xsel_pow]
      simp only [hk, decide_true, Bool.true_and]
      rw [← hv]
  · rintro ⟨s, -, rfl⟩
    have : xsel (row w m K) (fun k => (spanOf d w m K s).testBit (piv dw K k)) d =
        spanOf d w m K s := by
      rw [spanOf]
      exact xsel_congr (fun _ _ _ => rfl) fun k hk => by
        rw [← spanOf, spanOf_testBit_piv R hk]
    rw [this, Nat.xor_self]

theorem mem_spanList {v : Nat} : v ∈ spanList d w m K ↔ ∃ s < 2 ^ d, spanOf d w m K s = v := by
  unfold spanList
  simp [List.mem_map, List.mem_range]

theorem nodup_spanList (R : Rref d w m dw K) : (spanList d w m K).Nodup := by
  unfold spanList
  refine List.Nodup.map_on (fun s hs s' hs' h => ?_) List.nodup_range
  rw [List.mem_range] at hs hs'
  exact spanOf_inj R hs hs' h

theorem mem_spanTab {v : Nat} : v ∈ (spanTab d w m K).toList ↔ v ∈ spanList d w m K := by
  unfold spanTab
  rw [List.toList_toArray]
  exact (List.mergeSort_perm _ _).mem_iff

theorem spanOf_mem_span (hm : m = 2 ^ w - 1) {f : Nat → Nat} {Kh Kq : Nat}
    (Rq : Rref d w m dw Kq) (hmap : mapsK d w m dw f Kh Kq = true) (hf : Lin w f) (s : Nat) :
    ∃ s' < 2 ^ d, f (spanOf d w m Kh s) = spanOf d w m Kq s' := by
  have hr : ∀ k < d, ∃ t < 2 ^ d, spanOf d w m Kq t = f (row w m Kh k) := fun k hk =>
    (inSpan_iff Rq _).1 (CFSG.KS.allN_spec hmap k hk)
  rw [spanOf, hf.map_xsel fun k _ => row_lt hm k]
  have : ∀ n ≤ d, ∃ s' < 2 ^ d,
      xsel (fun k => f (row w m Kh k)) s.testBit n = spanOf d w m Kq s' := by
    intro n hn
    induction n with
    | zero => exact ⟨0, Nat.two_pow_pos d, spanOf_zero.symm⟩
    | succ n ih =>
      obtain ⟨s1, hs1, e1⟩ := ih (by omega)
      rw [xsel_succ, e1]
      split
      · obtain ⟨t, ht, et⟩ := hr n (by omega)
        refine ⟨s1 ^^^ t, Nat.xor_lt_two_pow hs1 ht, ?_⟩
        rw [← et, spanOf_xor]
      · exact ⟨s1, hs1, by rw [Nat.xor_zero]⟩
  exact this d le_rfl

theorem spanTab_map (hm : m = 2 ^ w - 1) {f : Nat → Nat} {Kh Kq : Nat} (Rh : Rref d w m dw Kh)
    (Rq : Rref d w m dw Kq) (hf : Lin w f) (h0 : ∀ a < 2 ^ w, f a = 0 → a = 0)
    (hmap : mapsK d w m dw f Kh Kq = true) :
    ((spanTab d w m Kh).toList.map f).mergeSort (· ≤ ·) = (spanTab d w m Kq).toList := by
  have p1 : List.Perm (spanTab d w m Kh).toList (spanList d w m Kh) := by
    unfold spanTab
    rw [List.toList_toArray]
    exact List.mergeSort_perm _ _
  have hnd : ((spanList d w m Kh).map f).Nodup := by
    refine List.Nodup.map_on (fun a ha b hb e => ?_) (nodup_spanList Rh)
    obtain ⟨s, -, rfl⟩ := mem_spanList.1 ha
    obtain ⟨s', -, rfl⟩ := mem_spanList.1 hb
    exact hf.inj h0 (spanOf_lt hm s) (spanOf_lt hm s') e
  have hsub : (spanList d w m Kh).map f ⊆ spanList d w m Kq := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
    obtain ⟨s, -, rfl⟩ := mem_spanList.1 hu
    obtain ⟨s', hs', e⟩ := spanOf_mem_span hm Rq hmap hf s
    exact mem_spanList.2 ⟨s', hs', e.symm⟩
  have hlen : (spanList d w m Kq).length ≤ ((spanList d w m Kh).map f).length := by
    simp [spanList]
  have p2 : List.Perm ((spanList d w m Kh).map f) (spanList d w m Kq) :=
    (List.subperm_of_subset hnd hsub).perm_of_length_le hlen
  have p3 : List.Perm (((spanTab d w m Kh).toList.map f).mergeSort (· ≤ ·))
      (spanTab d w m Kq).toList := by
    refine (List.mergeSort_perm _ _).trans ((p1.map f).trans (p2.trans ?_))
    unfold spanTab
    rw [List.toList_toArray]
    exact (List.mergeSort_perm _ _).symm
  refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2)
    (List.pairwise_mergeSort' _ _) ?_ p3
  unfold spanTab
  rw [List.toList_toArray]
  exact List.pairwise_mergeSort' _ _

theorem mapsK_of_map {f : Nat → Nat} (R : Rref d w m dw K)
    (h : ((spanTab d w m K).toList.map f).mergeSort (· ≤ ·) = (spanTab d w m K).toList) :
    mapsK d w m dw f K K = true := by
  apply CFSG.KS.Raw.Orb.allN_iff.2
  intro k hk
  rw [inSpan_iff R]
  have hrow : row w m K k ∈ (spanTab d w m K).toList :=
    mem_spanTab.2 (mem_spanList.2 ⟨2 ^ k, Nat.pow_lt_pow_right (by omega) hk,
      spanOf_pow hk⟩)
  have : f (row w m K k) ∈ (spanTab d w m K).toList := by
    rw [← h, (List.mergeSort_perm _ _).mem_iff]
    exact List.mem_map_of_mem hrow
  exact mem_spanList.1 (mem_spanTab.1 this)

@[expose] def HB (v p : Nat) : Prop := v.testBit p = true ∧ v < 2 ^ (p + 1)

theorem HB.unique {v p q : Nat} (h : HB v p) (h' : HB v q) : p = q := by
  have a : ∀ {p q}, HB v p → HB v q → p ≤ q := by
    intro p q hp hq
    by_contra hc
    have : v < 2 ^ p := lt_of_lt_of_le hq.2 (Nat.pow_le_pow_right (by omega) (by omega))
    have h1 := hp.1
    rw [Nat.testBit_lt_two_pow this] at h1
    exact Bool.false_ne_true h1
  exact Nat.le_antisymm (a h h') (a h' h)

theorem hb_spanOf (R : Rref d w m dw K) {s : Nat} (hs : s < 2 ^ d) (hs0 : s ≠ 0) :
    s.log2 < d ∧ HB (spanOf d w m K s) (piv dw K s.log2) := by
  have hl : s.log2 < d := (Nat.log2_lt hs0).2 hs
  refine ⟨hl, ?_, ?_⟩
  · rw [spanOf_testBit_piv R hl, Nat.testBit_log2 hs0]
  · refine xsel_lt fun k hk hc => lt_of_lt_of_le (R.row_lt k hk)
      (Nat.pow_le_pow_right (by omega) (Nat.succ_le_succ (R.piv_le ?_ hl)))
    by_contra hk'
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le Nat.lt_log2_self
      (Nat.pow_le_pow_right (by omega) (by omega)))] at hc
    exact Bool.false_ne_true hc

theorem hb_row (R : Rref d w m dw K) {k : Nat} (hk : k < d) : HB (row w m K k) (piv dw K k) :=
  ⟨R.piv_bit k hk, R.row_lt k hk⟩

theorem eq_of_fields {d w dw K K' : Nat} (hdw : dw = d * w) (hK : K < 2 ^ (dw + 8 * d))
    (hK' : K' < 2 ^ (dw + 8 * d)) (hr : ∀ k < d, row w (2 ^ w - 1) K k = row w (2 ^ w - 1) K' k)
    (hp : ∀ k < d, piv dw K k = piv dw K' k) : K = K' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < dw
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h | h
      · subst h
        omega
      · exact h
    have hq : i / w < d := by
      rw [Nat.div_lt_iff_lt_mul hw]
      rw [hdw] at hi
      exact hi
    have := congrArg (fun x => x.testBit (i % w)) (hr (i / w) hq)
    simp only [row] at this
    rw [testBit_fld, testBit_fld] at this
    simp only [Nat.mod_lt i hw, decide_true, Bool.true_and] at this
    have e : Nat.mul w (i / w) + i % w = i := Nat.div_add_mod i w
    rwa [e] at this
  · by_cases hi2 : i < dw + 8 * d
    · have hq : (i - dw) / 8 < d := by omega
      have := congrArg (fun x => x.testBit ((i - dw) % 8)) (hp ((i - dw) / 8) hq)
      simp only [piv] at this
      change (Nat.land (Nat.shiftRight K (Nat.add dw (Nat.shiftLeft ((i - dw) / 8) 3)))
          (2 ^ 8 - 1)).testBit _ =
        (Nat.land (Nat.shiftRight K' (Nat.add dw (Nat.shiftLeft ((i - dw) / 8) 3)))
          (2 ^ 8 - 1)).testBit _ at this
      rw [testBit_fld, testBit_fld] at this
      simp only [Nat.mod_lt _ (show 0 < 8 by omega), decide_true, Bool.true_and] at this
      have e1 : Nat.shiftLeft ((i - dw) / 8) 3 = (i - dw) / 8 * 2 ^ 3 := Nat.shiftLeft_eq _ _
      have e : Nat.add dw (Nat.shiftLeft ((i - dw) / 8) 3) + (i - dw) % 8 = i := by
        rw [e1]
        change dw + (i - dw) / 8 * 2 ^ 3 + (i - dw) % 8 = i
        omega
      rwa [e] at this
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hK (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hK' (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem spanTab_inj (hm : m = 2 ^ w - 1) (hdw : dw = d * w) {K' : Nat} (R : Rref d w m dw K)
    (R' : Rref d w m dw K') (h : spanTab d w m K = spanTab d w m K') : K = K' := by
  have hmem : ∀ v, (∃ s < 2 ^ d, spanOf d w m K s = v) ↔ ∃ s < 2 ^ d, spanOf d w m K' s = v :=
    fun v => by
      rw [← mem_spanList, ← mem_spanList, ← mem_spanTab, ← mem_spanTab, h]
  have hpiv : ∀ {A B : Nat}, Rref d w m dw A → Rref d w m dw B →
      (∀ v, (∃ s < 2 ^ d, spanOf d w m A s = v) → ∃ s < 2 ^ d, spanOf d w m B s = v) →
      ∀ k < d, ∃ l < d, piv dw A k = piv dw B l := by
    intro A B RA RB hAB k hk
    obtain ⟨s, hs, e⟩ := hAB _ ⟨2 ^ k, Nat.pow_lt_pow_right (by omega) hk, spanOf_pow hk⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [spanOf_zero] at e
      have := RA.piv_bit k hk
      rw [← e, Nat.zero_testBit] at this
      exact Bool.false_ne_true this
    obtain ⟨hl, hb⟩ := hb_spanOf RB hs hs0
    rw [e] at hb
    exact ⟨_, hl, (hb_row RA hk).unique hb⟩
  have hsm : ∀ {A : Nat}, Rref d w m dw A → StrictMono (fun k : Fin d => piv dw A k.val) :=
    fun RA a b hab => RA.piv_lt hab b.isLt
  have hrange : Set.range (fun k : Fin d => piv dw K k.val) =
      Set.range (fun k : Fin d => piv dw K' k.val) := by
    ext p
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨l, hl, e⟩ := hpiv R R' (fun v => (hmem v).1) k.val k.isLt
      exact ⟨⟨l, hl⟩, e.symm⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨l, hl, e⟩ := hpiv R' R (fun v => (hmem v).2) k.val k.isLt
      exact ⟨⟨l, hl⟩, e.symm⟩
  have hp : ∀ k < d, piv dw K k = piv dw K' k := fun k hk =>
    congrFun ((StrictMono.range_inj_of_wellFoundedLT (hsm R) (hsm R')).1 hrange) ⟨k, hk⟩
  have hr : ∀ k < d, row w m K k = row w m K' k := by
    intro k hk
    obtain ⟨s, hs, e⟩ := (hmem _).2 ⟨2 ^ k, Nat.pow_lt_pow_right (by omega) hk,
      spanOf_pow hk⟩
    have hs2 : s = 2 ^ k := eq_of_testBit_lt hs (Nat.pow_lt_pow_right (by omega) hk) fun j hj => by
      rw [← spanOf_testBit_piv R hj, e, hp j hj, Nat.testBit_two_pow]
      by_cases hjk : j = k
      · subst hjk
        simp [R'.piv_bit j hj]
      · simp [R'.off j hj k hk (fun e => hjk e.symm), show ¬ k = j from fun e => hjk e.symm]
    rw [← spanOf_pow hk, ← hs2, e]
  subst hm
  exact eq_of_fields hdw R.top R'.top hr hp

end CFSG.KC.XorSpan

end
