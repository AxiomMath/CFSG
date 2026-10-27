module

public import CFSG.Certificates.Kernel.SporSch.LySylDefs
import CFSG.Certificates.Kernel.SporSch.LyLoop
public import CFSG.Sporadic.Schreier.LyCheckSylow

public section

namespace CFSG.KS.SporSch.LySylP.Table

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.SporSch.LyM CFSG.Sporadic.LySchreier.Native
open CFSG.KS.SporSch.LySyl CFSG.KS.SporSch.LyLoop

private theorem band {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

private theorem bl {a b : Nat} (h : Nat.blt a b = true) : a < b := Eq.mp Nat.blt_eq h

private theorem be {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

private theorem allBlk_eq (b : Nat) (f : Nat → Bool) (len : Nat) :
    allBlk b f len = (List.range len).all fun l => f (b + l) := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have hs : allBlk b f (len + 1) = (f (b + len) && allBlk b f len) := bAnd_eqP _ _
    rw [hs, List.range_succ, List.all_append, ← ih, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_comm]

private theorem all_range_add (f : Nat → Bool) (a b : Nat) :
    (List.range (a + b)).all f
      = ((List.range a).all f && (List.range b).all fun l => f (a + l)) := by
  simp only [List.range_add, List.all_append, List.all_map, Function.comp_def]

private theorem shiftLeft_six (x : Nat) : Nat.shiftLeft x (nat_lit 6) = x * 64 := by
  change x <<< 6 = _
  rw [Nat.shiftLeft_eq]

private theorem allN_eq (n : Nat) (f : Nat → Bool) : allN n f = (List.range n).all f := by
  have hrec : ∀ h, Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) h
      = (List.range (h * 64)).all f := by
    intro h
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
        bAnd_eqP _ _
      have e : (h + 1) * 64 = h * 64 + 64 := by omega
      rw [hs, ih, allBlk_eq, shiftLeft_six h, e, all_range_add f (h * 64) 64, Bool.and_comm]
  have hs : allN n f = (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) &&
        Nat.rec (motive := fun _ => Bool) true
          (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
            (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64)))
          (Nat.shiftRight n (nat_lit 6))) :=
    bAnd_eqP _ _
  have hsr : Nat.shiftRight n 6 = n / 64 := by
    change n >>> 6 = _
    rw [Nat.shiftRight_eq_div_pow]
  have hla : Nat.land n 63 = n % 64 := by
    change n &&& 63 = _
    have h63 : (63 : Nat) = 2 ^ 6 - 1 := rfl
    rw [h63, Nat.and_two_pow_sub_one_eq_mod]
  have e : n / 64 * 64 + n % 64 = n := by omega
  rw [hs, hrec, allBlk_eq, shiftLeft_six, hla, hsr, Bool.and_comm,
    ← all_range_add f (n / 64 * 64) (n % 64), e]

private theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  rw [allN_eq, List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.2 hi), fun h x hx => h x (List.mem_range.1 hx)⟩

private theorem anyN_iff {n : Nat} {f : Nat → Bool} :
    CFSG.KS.SporSch.anyN n f = true ↔ ∃ i < n, f i = true := by
  unfold CFSG.KS.SporSch.anyN
  rw [bIf_eqP]
  constructor
  · intro h
    refine Classical.byContradiction fun hne => ?_
    have hall : allN n (fun i => Bool.rec (motive := fun _ => Bool) true false (f i)) = true := by
      rw [allN_iff]
      intro i hi
      cases hf : f i
      · rfl
      · exact absurd ⟨i, hi, hf⟩ hne
    rw [hall] at h
    exact absurd h (by decide)
  · rintro ⟨i, hi, hf⟩
    cases hall : allN n (fun i => Bool.rec (motive := fun _ => Bool) true false (f i))
    · rfl
    · have := allN_iff.1 hall i hi
      rw [hf] at this
      exact absurd this (by decide)

private theorem allIn_iff {lo hi : Nat} {p : Nat → Bool} :
    CFSG.Sporadic.Th.Native.allIn lo hi p = true ↔ ∀ k, lo ≤ k → k < hi → p k = true := by
  unfold CFSG.Sporadic.Th.Native.allIn
  have key : ∀ m, Nat.all m (fun k _ => p (lo + k)) = true ↔ ∀ k < m, p (lo + k) = true := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.all_succ, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
        · exact h1 k h
        · subst h; exact h2
      · intro h
        exact ⟨fun k hk => h k (by omega), h m (by omega)⟩
  rw [key]
  constructor
  · intro h k h1 h2
    have := h (k - lo) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  · intro h k hk
    exact h (lo + k) (by omega) (by omega)

private theorem hasBit_iff (M l : Nat) : hasBit M l = true ↔ M.testBit l = true := by
  have e1 : Nat.shiftLeft 1 l = 2 ^ l := Nat.one_shiftLeft l
  change Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 l)) = true ↔ _
  rw [e1, Nat.blt_eq]
  change 0 < M &&& 2 ^ l ↔ _
  rw [Nat.and_two_pow]
  cases M.testBit l <;> simp [Nat.two_pow_pos]

private theorem testBit_maskL (L : List Nat) (i : Nat) : (maskL L).testBit i = true ↔ i ∈ L := by
  induction L with
  | nil => change (0 : Nat).testBit i = true ↔ _; simp
  | cons x L ih =>
    change ((maskL L) ||| (1 <<< x)).testBit i = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih,
      decide_eq_true_iff, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

private theorem hasBit_maskL (L : List Nat) (i : Nat) : hasBit (maskL L) i = true ↔ i ∈ L := by
  rw [hasBit_iff, testBit_maskL]

private theorem testBit_foldr (g : Nat → Nat) (i : Nat) : ∀ l : List Nat,
    (l.foldr (fun k acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (g k))) (nat_lit 0)).testBit i
      = true ↔ ∃ k ∈ l, g k = i
  | [] => by change (0 : Nat).testBit i = true ↔ _; simp
  | x :: l => by
    rw [List.foldr_cons]
    change ((l.foldr (fun k acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (g k))) (nat_lit 0))
      ||| (1 <<< g x)).testBit i = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, testBit_foldr g i l,
      decide_eq_true_iff]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact Or.comm

private theorem hasBit_dMask (DT : Nat → Nat) (nD x : Nat) :
    hasBit (dMask DT nD) x = true ↔ ∃ k < nD, b8 (DT k) 0 = x := by
  rw [hasBit_iff]
  unfold dMask
  rw [foldN_eqP, testBit_foldr (fun k => b8 (DT k) 0) x]
  simp only [List.mem_range]

private theorem memD (DT : Nat → Nat) (nD x : Nat) :
    x ∈ (Array.ofFn (n := nD) fun k => b8 (DT k.val) 0).toList ↔ hasBit (dMask DT nD) x = true := by
  rw [hasBit_dMask, Array.toList_ofFn, List.mem_ofFn]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

private theorem popN_eq (M n : Nat) :
    popN M n = ((List.range n).filter fun i => hasBit M i).length := by
  unfold popN
  rw [foldN_eqP]
  generalize List.range n = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, List.filter_cons, nIf_eqP]
    cases hasBit M a <;> simp

private theorem lenL_eq (L : List Nat) : LySyl.lenL L = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih => exact congrArg Nat.succ ih

private theorem nodup_of_popN {L : List Nat} {M n : Nat}
    (hmem : ∀ x, hasBit M x = true ↔ x ∈ L) (hp : popN M n = L.length) : L.Nodup := by
  rw [popN_eq] at hp
  have hF : ((List.range n).filter fun i => hasBit M i).Nodup := List.nodup_range.filter _
  have hsub : ((List.range n).filter fun i => hasBit M i) ⊆ L :=
    fun x hx => (hmem x).1 (List.mem_filter.1 hx).2
  exact ((hF.subperm hsub).perm_of_length_le (by omega)).nodup_iff.1 hF

private theorem ite_true_iff (c : Bool) (t : Bool) :
    ((if c = true then t else true) = true) ↔ (c = true → t = true) := by
  cases c <;> simp

private theorem ite_false_iff (c : Bool) (t : Bool) :
    ((if c = true then true else t) = true) ↔ (c = false → t = true) := by
  cases c <;> simp

private theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

private theorem beq01 {a b : Bool}
    (h : Nat.beq (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) a)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem tm_eq {MT : Nat → Nat} {n i j : Nat} (hi : i < n) (hj : j < n) :
    tm (TBL MT n) i j = tmK MT i j := by
  unfold tm TBL
  rw [ofFn_getP (fun i => Array.ofFn (n := n) fun j => tmK MT i j.val) hi,
    ofFn_getP (fun j => tmK MT i j) hj]

private theorem ivOK_spec {MT : Nat → Nat} {IV n i : Nat} (h : ivOK MT IV n i = true) :
    tinvK IV i < n ∧ tmK MT i (tinvK IV i) = 0 ∧ ∀ j < tinvK IV i, tmK MT i j ≠ 0 := by
  unfold ivOK at h
  rw [strictB_eqB] at h
  obtain ⟨h1, h2⟩ := band h
  obtain ⟨h2, h3⟩ := band h2
  refine ⟨bl h1, be h2, fun j hj e => ?_⟩
  have := allN_iff.1 h3 j hj
  rw [e] at this
  exact absurd this (by decide)

private theorem tinv_eq {MT : Nat → Nat} {IV n i : Nat} (hi : i < n) (h : ivOK MT IV n i = true) :
    tinv (TBL MT n) n i = tinvK IV i := by
  obtain ⟨h1, h2, h3⟩ := ivOK_spec h
  unfold tinv
  have e : (List.range n).find? (fun j => tm (TBL MT n) i j == 0) = some (tinvK IV i) := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, List.mem_range.2 h1, fun j hj => ?_⟩
    · rw [tm_eq hi h1, h2]
      rfl
    · rw [tm_eq hi (by omega)]
      simpa using h3 j hj
  rw [e]
  rfl

private theorem tpowK_succ (MT : Nat → Nat) (i e : Nat) :
    tpowK MT i (e + 1) = tmK MT (tpowK MT i e) i :=
  strictN_eqP (tpowK MT i e) (fun a => tmK MT a i)

private theorem tpow_eq {MT : Nat → Nat} {n : Nat} (hrows : ∀ i < n, ∀ j < n, tmK MT i j < n)
    (hn : 0 < n) {x : Nat} (hx : x < n) :
    ∀ e, tpow (TBL MT n) x e = tpowK MT x e ∧ tpowK MT x e < n
  | 0 => ⟨rfl, hn⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := tpow_eq hrows hn hx e
    rw [tpowK_succ]
    refine ⟨?_, hrows _ h2 _ hx⟩
    change tm (TBL MT n) (tpow (TBL MT n) x e) x = _
    rw [h1, tm_eq h2 hx]

private theorem nbeq {a b : Nat} : (a == b) = Nat.beq a b := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff]

private theorem zc (p : Nat) :
    [0, 6].contains p = Bool.rec (motive := fun _ => Bool) (Nat.beq p 6) true (Nat.beq p 0) := by
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, nbeq]
  cases Nat.beq p 0 <;> rfl

private theorem ord8_eq {MT : Nat → Nat} {n : Nat} (hrows : ∀ i < n, ∀ j < n, tmK MT i j < n)
    (hn : 0 < n) {x : Nat} (hx : x < n) : ord8Mod (TBL MT n) [0, 6] x = ord8K MT x := by
  have h4 := (tpow_eq hrows hn hx 4).1
  have h8 := (tpow_eq hrows hn hx 8).1
  have e8 : tpowK MT x 8 = tmK MT (tmK MT (tmK MT (tmK MT (tpowK MT x 4) x) x) x) x := by
    rw [show (8 : Nat) = 4 + 1 + 1 + 1 + 1 from rfl, tpowK_succ, tpowK_succ, tpowK_succ,
      tpowK_succ]
  unfold ord8Mod
  rw [h4, h8, e8]
  unfold ord8K
  rw [strictB_eqB, strictB_eqB]
  generalize tpowK MT x 4 = p4
  generalize tmK MT (tmK MT (tmK MT (tmK MT p4 x) x) x) x = p8
  rw [zc p8, zc p4]
  exact (bAnd_eqP _ _).symm


private theorem tcomm_eq {MT : Nat → Nat} {IV n : Nat} (hrows : ∀ i < n, ∀ j < n, tmK MT i j < n)
    (hiv : ∀ i < n, ivOK MT IV n i = true) {a b : Nat} (ha : a < n) (hb : b < n) :
    tcomm (TBL MT n) n a b = tcommK MT IV a b := by
  have ia := (ivOK_spec (hiv a ha)).1
  have ib := (ivOK_spec (hiv b hb)).1
  unfold tcomm tcommK
  rw [tinv_eq ha (hiv a ha), tinv_eq hb (hiv b hb), tm_eq ha hb, tm_eq (hrows a ha b hb) ia,
    tm_eq (hrows _ (hrows a ha b hb) _ ia) ib]

private theorem allLtN_iff (n : Nat) : ∀ L : List Nat,
    CFSG.KS.Mathieu.allLtN n L = true ↔ ∀ x ∈ L, x < n
  | [] => by simp [CFSG.KS.Mathieu.allLtN]
  | x :: L => by
    have e : CFSG.KS.Mathieu.allLtN n (x :: L) = (Nat.blt x n && CFSG.KS.Mathieu.allLtN n L) :=
      bAnd_eqP _ _
    rw [e, Bool.and_eq_true, allLtN_iff n L, blt_iff, List.forall_mem_cons]

private theorem bor_iff (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) b true a = true ↔ a = true ∨ b = true := by
  cases a <;> simp

private theorem closedM_spec {MT : Nat → Nat} {n M : Nat} (h : closedM MT n M = true) :
    ∀ a < n, hasBit M a = true → ∀ b < n, hasBit M b = true → hasBit M (tmK MT a b) = true := by
  intro a ha hA b hb hB
  unfold closedM at h
  have h1 := allN_iff.1 h a ha
  rw [bIf_eqP, if_pos hA] at h1
  have h2 := allN_iff.1 h1 b hb
  rwa [bIf_eqP, if_pos hB] at h2

private theorem rowChk_spec {MT : Nat → Nat} {IV n DM i : Nat} (h : rowChk MT IV n DM i = true) :
    ivOK MT IV n i = true ∧
    ((∀ j < n, tmK MT i j = tmK MT j i) ↔ (i = 0 ∨ i = 6)) ∧
    (∀ b < n, hasBit DM (tcommK MT IV i b) = true) ∧ hasBit DM (tmK MT i i) = true ∧
    (hasBit DM i = false → (∀ d < n, hasBit DM d = true → ord8K MT (tmK MT i d) = true) →
      hasBit DM (tmK MT (tinvK IV 38) i) = true) := by
  unfold rowChk at h
  obtain ⟨h1, h⟩ := band h
  obtain ⟨h2, h⟩ := band h
  obtain ⟨h3, h⟩ := band h
  obtain ⟨h4, h5⟩ := band h
  refine ⟨h1, ?_, allN_iff.1 h3, h4, fun hn hall => ?_⟩
  · have e := beq01 h2
    have e2 : (∀ j < n, tmK MT i j = tmK MT j i) ↔
        allN n (fun j => Nat.beq (tmK MT i j) (tmK MT j i)) = true := by
      rw [allN_iff]
      exact forall₂_congr fun j _ => beq_iff.symm
    rw [e2, e, bor_iff, beq_iff, beq_iff]
  · rw [bIf_eqP, if_neg (by rw [hn]; decide), bIf_eqP, if_pos] at h5
    · exact h5
    · rw [allN_iff]
      intro d hd
      rw [bIf_eqP]
      split
      · exact hall d hd ‹_›
      · rfl

private theorem dChk_spec {MT DT : Nat → Nat} {IV n nD : Nat} (h : dChk MT IV n DT nD = true) :
    nD = 32 ∧ b8 (DT 0) 0 = 0 ∧ popN (dMask DT nD) n = nD ∧ closedM MT n (dMask DT nD) = true ∧
    hasBit (dMask DT nD) 0 = true ∧ hasBit (dMask DT nD) 6 = true ∧
    (∀ k < nD, b8 (DT k) 0 < n ∧ hasBit (dMask DT nD) (tinvK IV (b8 (DT k) 0)) = true) ∧
    (∀ k < nD, k ≠ 0 → b8 (DT k) 1 < k ∧ b8 (DT k) 2 < n ∧ b8 (DT k) 3 < n ∧
      tmK MT (tcommK MT IV (b8 (DT k) 2) (b8 (DT k) 3)) (b8 (DT (b8 (DT k) 1)) 0) = b8 (DT k) 0) ∧
    38 < n ∧ hasBit (dMask DT nD) 38 = false ∧
    ∀ k < nD, ord8K MT (tmK MT 38 (b8 (DT k) 0)) = true := by
  unfold dChk at h
  rw [strictB_eqB] at h
  obtain ⟨h1, h⟩ := band h
  obtain ⟨h2, h⟩ := band h
  obtain ⟨h3, h⟩ := band h
  obtain ⟨_, h⟩ := band h
  obtain ⟨h5, h⟩ := band h
  obtain ⟨h6, h⟩ := band h
  obtain ⟨h7, h⟩ := band h
  obtain ⟨h8, h⟩ := band h
  obtain ⟨h9, h⟩ := band h
  obtain ⟨h10, h⟩ := band h
  obtain ⟨h11, h12⟩ := band h
  refine ⟨be h1, be h2, be h3, h5, h6, h7, fun k hk => ?_, fun k hk hk0 => ?_, bl h10, ?_,
    allN_iff.1 h12⟩
  · obtain ⟨a, b⟩ := band (allN_iff.1 h8 k hk)
    exact ⟨bl a, b⟩
  · have := allN_iff.1 h9 k hk
    rw [bIf_eqP, if_neg (fun e => hk0 (be e))] at this
    obtain ⟨a, this⟩ := band this
    obtain ⟨b, this⟩ := band this
    obtain ⟨c, d⟩ := band this
    exact ⟨bl a, bl b, bl c, be d⟩
  · cases e : hasBit (dMask DT nD) 38
    · rfl
    · rw [e] at h11
      exact absurd h11 (by decide)


private theorem extendsBy_eq {MT : Nat → Nat} {n x : Nat} {E : List Nat} (hE : ∀ e ∈ E, e < n)
    (hx : x < n) : extendsBy (TBL MT n) E x = extK MT n (maskL E) x := by
  apply Bool.eq_iff_iff.2
  unfold extendsBy isInv extK
  rw [bAnd_eqP, bAnd_eqP, bAnd_eqP]
  simp only [Bool.and_eq_true, Bool.not_eq_true', allN_iff, List.all_eq_true, tm_eq hx hx,
    hasBit_maskL]
  have c1 : (x != 0) = true ↔ Nat.beq x 0 = false := by
    simp only [bne, nbeq, Bool.not_eq_true']
  have c2 : (tmK MT x x == 0) = true ↔ Nat.beq (tmK MT x x) 0 = true := by rw [nbeq]
  have c3 : E.contains x = false ↔ hasBit (maskL E) x = false := by
    rw [← Bool.not_eq_true, ← Bool.not_eq_true, hasBit_maskL, List.contains_iff_mem]
  have c4 : (∀ e ∈ E, (tm (TBL MT n) x e == tm (TBL MT n) e x) = true) ↔ ∀ i < n,
      Bool.rec (motive := fun _ => Bool) true (Nat.beq (tmK MT x i) (tmK MT i x))
        (hasBit (maskL E) i) = true := by
    constructor
    · intro h i hi
      rw [bIf_eqP]
      split
      · have := h i ((hasBit_maskL E i).1 ‹_›)
        rw [tm_eq hx hi, tm_eq hi hx, nbeq] at this
        exact this
      · rfl
    · intro h e he
      have := h e (hE e he)
      rw [bIf_eqP, if_pos ((hasBit_maskL E e).2 he)] at this
      rw [tm_eq hx (hE e he), tm_eq (hE e he) hx, nbeq]
      exact this
  rw [c1, c2, c3, c4, and_assoc, and_assoc]

private theorem eChk_spec {MT : Nat → Nat} {n : Nat} {L : List Nat} (h : eChk MT n L = true) :
    L.length = 16 ∧ popN (maskL L) n = 16 ∧ (∀ x ∈ L, x < n) ∧ closedM MT n (maskL L) = true ∧
    0 ∈ L ∧ (∀ x ∈ L, x ≠ 0 → tmK MT x x = 0) ∧ (∀ a ∈ L, ∀ b ∈ L, tmK MT a b = tmK MT b a) ∧
    ∀ x < n, extK MT n (maskL L) x = false := by
  unfold eChk at h
  rw [strictB_eqB] at h
  obtain ⟨h1, h⟩ := band h
  obtain ⟨h2, h⟩ := band h
  obtain ⟨h3, h⟩ := band h
  obtain ⟨h4, h⟩ := band h
  obtain ⟨h5, h⟩ := band h
  obtain ⟨h6, h⟩ := band h
  obtain ⟨h7, h8⟩ := band h
  have hlt := (allLtN_iff n L).1 h3
  refine ⟨(lenL_eq L).symm.trans (be h1), be h2, hlt, h4, (hasBit_maskL L 0).1 h5,
    fun x hx hx0 => ?_, fun a ha b hb => ?_, fun x hx => ?_⟩
  · have := allN_iff.1 h6 x (hlt x hx)
    rw [bIf_eqP, if_pos ((hasBit_maskL L x).2 hx), bIf_eqP,
      if_neg (fun e => hx0 (be e))] at this
    exact be this
  · have := allN_iff.1 h7 a (hlt a ha)
    rw [bIf_eqP, if_pos ((hasBit_maskL L a).2 ha)] at this
    have := allN_iff.1 this b (hlt b hb)
    rw [bIf_eqP, if_pos ((hasBit_maskL L b).2 hb)] at this
    exact be this
  · have := allN_iff.1 h8 x hx
    simpa using this

private theorem qChk_spec {MT : Nat → Nat} {IV n f : Nat} {Q E0 E1 : List Nat}
    (h : qChk MT IV n Q E0 E1 f = true) :
    Q.length = 64 ∧ popN (maskL Q) n = 64 ∧ (∀ x ∈ Q, x < n) ∧ closedM MT n (maskL Q) = true ∧
    0 ∈ Q ∧
    (∀ q ∈ Q, tinvK IV q ∈ Q ∧ (∃ a ∈ E0, ∃ b ∈ E1, tmK MT a b = q) ∧
      ((∀ r ∈ Q, tmK MT q r = tmK MT r q) ↔ (q = 0 ∨ q = 6 ∨ q = 113 ∨ q = 207))) ∧
    (∀ x ∈ E0, x ∈ Q) ∧ (∀ x ∈ E1, x ∈ Q) ∧
    (∀ q < n, (q = 0 ∨ q = 6 ∨ q = 113 ∨ q = 207) → q ∈ Q ∧ tmK MT q q = 0) ∧ f ∈ Q := by
  unfold qChk at h
  rw [strictB_eqB, strictB_eqB, strictB_eqB] at h
  obtain ⟨h1, h⟩ := band h
  obtain ⟨h2, h⟩ := band h
  obtain ⟨h3, h⟩ := band h
  obtain ⟨h4, h⟩ := band h
  obtain ⟨h5, h⟩ := band h
  obtain ⟨h6, h⟩ := band h
  obtain ⟨h7, h⟩ := band h
  obtain ⟨h8, h⟩ := band h
  obtain ⟨h9, h10⟩ := band h
  have hlt := (allLtN_iff n Q).1 h3
  have sub : ∀ {E : List Nat}, Nat.beq (Nat.land (maskL E) (maskL Q)) (maskL E) = true →
      ∀ x ∈ E, x ∈ Q := by
    intro E hE x hx
    have e := congrArg (fun m => m.testBit x) (be hE)
    change (maskL E &&& maskL Q).testBit x = (maskL E).testBit x at e
    rw [Nat.testBit_and, (testBit_maskL E x).2 hx, Bool.true_and] at e
    exact (testBit_maskL Q x).1 e
  refine ⟨(lenL_eq Q).symm.trans (be h1), be h2, hlt, h4, (hasBit_maskL Q 0).1 h5,
    fun q hq => ?_, sub h7, sub h8, fun q hq hz => ?_, (hasBit_maskL Q f).1 h10⟩
  · have := allN_iff.1 h6 q (hlt q hq)
    rw [bIf_eqP, if_pos ((hasBit_maskL Q q).2 hq)] at this
    obtain ⟨a, this⟩ := band this
    obtain ⟨b, c⟩ := band this
    refine ⟨(hasBit_maskL Q _).1 a, ?_, ?_⟩
    · obtain ⟨a, -, ha⟩ := anyN_iff.1 b
      rw [bIf_eqP] at ha
      split at ha
      · obtain ⟨b, -, hb⟩ := anyN_iff.1 ha
        rw [bIf_eqP] at hb
        split at hb
        · exact ⟨a, (hasBit_maskL E0 a).1 ‹_›, b, (hasBit_maskL E1 b).1 ‹_›, be hb⟩
        · exact absurd hb (by decide)
      · exact absurd ha (by decide)
    · have e := beq01 c
      have e2 : (∀ r ∈ Q, tmK MT q r = tmK MT r q) ↔ allN n (fun r =>
          Bool.rec (motive := fun _ => Bool) true (Nat.beq (tmK MT q r) (tmK MT r q))
            (hasBit (maskL Q) r)) = true := by
        rw [allN_iff]
        constructor
        · intro hc r hr
          rw [bIf_eqP]
          split
          · exact beq_iff.2 (hc r ((hasBit_maskL Q r).1 ‹_›))
          · rfl
        · intro hc r hr
          have := hc r (hlt r hr)
          rw [bIf_eqP, if_pos ((hasBit_maskL Q r).2 hr)] at this
          exact be this
      rw [e2, e, bor_iff, bor_iff, bor_iff, beq_iff, beq_iff, beq_iff, beq_iff]
  · have := allN_iff.1 h9 q hq
    rw [bIf_eqP, if_pos] at this
    · obtain ⟨a, b⟩ := band this
      exact ⟨(hasBit_maskL Q q).1 a, be b⟩
    · rw [bor_iff, bor_iff, bor_iff, beq_iff, beq_iff, beq_iff, beq_iff]
      exact hz


private theorem closedOK_of {MT : Nat → Nat} {n M : Nat} {L : List Nat}
    (hmem : ∀ x, x ∈ L ↔ hasBit M x = true) (hlt : ∀ x ∈ L, x < n)
    (hcl : closedM MT n M = true) : closedOK (TBL MT n) L = true := by
  unfold closedOK
  simp only [List.all_eq_true, List.contains_iff_mem]
  intro a ha b hb
  rw [tm_eq (hlt a ha) (hlt b hb), hmem]
  exact closedM_spec hcl a (hlt a ha) ((hmem a).1 ha) b (hlt b hb) ((hmem b).1 hb)

private theorem eSet {MT : Nat → Nat} {n : Nat} {E : List Nat} (he : eChk MT n E = true) :
    ((List.range n).all fun x => !extendsBy (TBL MT n) E x) = true ∧
    (closedOK (TBL MT n) E && E.contains 0 && E.all fun x => x == 0 || isInv (TBL MT n) x) = true ∧
    (E.all fun a => E.all fun b => tm (TBL MT n) a b == tm (TBL MT n) b a) = true ∧
    (E.length == 16 && decide E.Nodup && E.all fun x => decide (x < n)) = true := by
  obtain ⟨hlen, hpop, hlt, hcl, h0, hinv, hcomm, hext⟩ := eChk_spec he
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro x hx
    rw [List.mem_range] at hx
    rw [extendsBy_eq hlt hx, hext x hx]
    rfl
  · simp only [Bool.and_eq_true]
    refine ⟨⟨closedOK_of (fun x => (hasBit_maskL E x).symm) hlt hcl,
      List.contains_iff_mem.2 h0⟩, ?_⟩
    rw [List.all_eq_true]
    intro x hx
    unfold isInv
    by_cases hx0 : x = 0
    · simp [hx0]
    · rw [tm_eq (hlt x hx) (hlt x hx), hinv x hx hx0]
      simp [hx0]
  · simp only [List.all_eq_true, beq_iff_eq]
    intro a ha b hb
    rw [tm_eq (hlt a ha) (hlt b hb), tm_eq (hlt b hb) (hlt a ha)]
    exact hcomm a ha b hb
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true]
    exact ⟨⟨hlen, nodup_of_popN (hasBit_maskL E) (by rw [hpop, hlen])⟩, hlt⟩

theorem table_sound {n nD : Nat} {MT DT : Nat → Nat} {IV : Nat} {L1 L2 L3 L4 : List (List Nat)}
    (hn : n = 256) (hiv : ∀ i < n, rowChk MT IV n (dMask DT nD) i = true)
    (hrows : ∀ i < n, ∀ j < n, tmK MT i j < n)
    (hd : dChk MT IV n DT nD = true) (hL4 : L4 = [(e16 ())[0]!.toList, (e16 ())[1]!.toList])
    (he0 : eChk MT n (L4.getD 0 []) = true) (he1 : eChk MT n (L4.getD 1 []) = true)
    (hq : qChk MT IV n qIndices.toList (L4.getD 0 []) (L4.getD 1 []) (fIndex ()) = true)
    (h1 : extOK (TBL MT n) n [[0]] L1 = true) (h2 : extOK (TBL MT n) n L1 L2 = true)
    (h3 : extOK (TBL MT n) n L2 L3 = true) (h4 : extOK (TBL MT n) n L3 L4 = true) :
    tableOK (TBL MT n) n (Array.ofFn (n := nD) fun k => b8 (DT k.val) 0)
      (Array.ofFn (n := nD) fun k => b8 (DT k.val) 1) (Array.ofFn (n := nD) fun k => b8 (DT k.val) 2)
      (Array.ofFn (n := nD) fun k => b8 (DT k.val) 3) L1 L2 L3 L4 38 = true := by
  obtain ⟨hD32, hD0, hpop, hclos, h0D, h6D, hDinv, hDtree, h38, h38D, hord⟩ := dChk_spec hd
  subst hD32 hL4
  have hR := fun i hi => rowChk_spec (hiv i hi)
  have hivk : ∀ i < n, ivOK MT IV n i = true := fun i hi => (hR i hi).1
  have hn0 : 0 < n := by omega
  have hinvlt : ∀ i < n, tinvK IV i < n := fun i hi => (ivOK_spec (hivk i hi)).1
  have htinv : ∀ i < n, tinv (TBL MT n) n i = tinvK IV i := fun i hi => tinv_eq hi (hivk i hi)
  have htc : ∀ a < n, ∀ b < n, tcomm (TBL MT n) n a b = tcommK MT IV a b :=
    fun a ha b hb => tcomm_eq hrows hivk ha hb
  have hclt : ∀ a < n, ∀ b < n, tcommK MT IV a b < n := fun a ha b hb =>
    hrows _ (hrows _ (hrows a ha b hb) _ (hinvlt a ha)) _ (hinvlt b hb)
  have hDg : ∀ c, ∀ k < 32, (Array.ofFn (n := 32) fun j => b8 (DT j.val) c)[k]! = b8 (DT k) c :=
    fun c k hk => ofFn_getP (fun j => b8 (DT j) c) hk
  have hmD := memD DT 32
  have hDlt : ∀ x ∈ (Array.ofFn (n := 32) fun k => b8 (DT k.val) 0).toList, x < n := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (hasBit_dMask DT 32 x).1 ((hmD x).1 hx)
    exact (hDinv k hk).1
  have hE0 := eSet he0
  have hE1 := eSet he1
  obtain ⟨hlt0, -⟩ := (eChk_spec he0).2.2
  obtain ⟨hlt1, -⟩ := (eChk_spec he1).2.2
  obtain ⟨hQlen, hQpop, hQlt, hQcl, hQ0, hQ, hsub0, hsub1, hZ, hf⟩ := qChk_spec hq
  simp only [tableOK, Bool.and_eq_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h1, h2, h3, h4,
    beq_self_eq_true _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    decide_eq_true h38, ?_, ?_, ?_⟩
  · rw [allIn_iff]
    intro i _ hi
    rw [htinv i hi, tm_eq hi (hinvlt i hi), (ivOK_spec (hivk i hi)).2.1]
    simp [hinvlt i hi]
  · rw [allIn_iff]
    intro i _ hi
    rw [beq_iff_eq]
    apply Bool.eq_iff_iff.2
    rw [allIn_iff, List.contains_iff_mem]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    refine Iff.trans ?_ (hR i hi).2.1
    exact ⟨fun h j hj => by
        have := h j (Nat.zero_le _) hj
        rwa [beq_iff_eq, tm_eq hi hj, tm_eq hj hi] at this,
      fun h j _ hj => by rw [beq_iff_eq, tm_eq hi hj, tm_eq hj hi]; exact h j hj⟩
  · simp only [Array.size_ofFn, beq_self_eq_true]
  · rw [hDg 0 0 (by omega), hD0]
    rfl
  · apply decide_eq_true
    exact nodup_of_popN (fun x => (hmD x).symm)
      (by rw [hpop, Array.length_toList, Array.size_ofFn])
  · exact closedOK_of hmD hDlt hclos
  · rw [List.contains_iff_mem, hmD]
    exact h0D
  · rw [List.contains_iff_mem, hmD]
    exact h6D
  · rw [allIn_iff]
    intro a _ ha
    rw [allIn_iff]
    intro b _ hb
    rw [htc a ha b hb, List.contains_iff_mem, hmD]
    exact (hR a ha).2.2.1 b hb
  · simp only [Array.size_ofFn, beq_self_eq_true]
  · simp only [Array.size_ofFn, beq_self_eq_true]
  · simp only [Array.size_ofFn, beq_self_eq_true]
  · rw [allIn_iff]
    intro k hk1 hk2
    obtain ⟨a, b, c, d⟩ := hDtree k hk2 (by omega)
    rw [hDg 1 k hk2, hDg 2 k hk2, hDg 3 k hk2, hDg 0 k hk2, hDg 0 _ (by omega)]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨⟨a, b⟩, c⟩, ?_⟩
    rw [htc _ b _ c, tm_eq (hclt _ b _ c) (hDinv _ (by omega)).1]
    exact d
  · rw [allIn_iff]
    intro i _ hi
    rw [tm_eq hi hi, List.contains_iff_mem, hmD]
    exact (hR i hi).2.2.2.1
  · rw [List.all_eq_true]
    intro x hx
    exact decide_eq_true (hDlt x hx)
  · rw [List.all_eq_true]
    intro d hd
    rw [htinv d (hDlt d hd), List.contains_iff_mem, hmD]
    obtain ⟨k, hk, rfl⟩ := (hasBit_dMask DT 32 d).1 ((hmD d).1 hd)
    exact (hDinv k hk).2
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨hE0.1, hE1.1⟩
  · rw [List.all_cons, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨hE0.2.1, hE1.2.1⟩
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨hE0.2.2.1, hE1.2.2.1⟩
  · rw [List.all_cons, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨hE0.2.2.2, hE1.2.2.2⟩
  · rw [beq_iff_eq]
    exact hQlen
  · exact decide_eq_true (nodup_of_popN (hasBit_maskL _) (by rw [hQpop, hQlen]))
  · rw [List.all_eq_true]
    intro x hx
    exact decide_eq_true (hQlt x hx)
  · exact closedOK_of (fun x => (hasBit_maskL _ x).symm) hQlt hQcl
  · exact List.contains_iff_mem.2 hQ0
  · rw [List.all_eq_true]
    intro q hq
    rw [htinv q (hQlt q hq), List.contains_iff_mem]
    exact (hQ q hq).1
  · rw [List.all_eq_true]
    intro q hq
    obtain ⟨a, ha, b, hb, hab⟩ := (hQ q hq).2.1
    rw [List.any_eq_true]
    refine ⟨a, ha, ?_⟩
    rw [List.any_eq_true]
    refine ⟨b, hb, ?_⟩
    rw [beq_iff_eq, tm_eq (hlt0 a ha) (hlt1 b hb)]
    exact hab
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true,
      List.contains_iff_mem]
    exact ⟨hsub0, hsub1⟩
  · rw [List.all_eq_true]
    intro q hq
    rw [beq_iff_eq]
    apply Bool.eq_iff_iff.2
    rw [List.all_eq_true, List.contains_iff_mem]
    simp only [List.mem_cons, List.not_mem_nil, or_false, beq_iff_eq]
    refine Iff.trans ?_ (hQ q hq).2.2
    exact forall₂_congr fun r hr => by rw [tm_eq (hQlt q hq) (hQlt r hr), tm_eq (hQlt r hr) (hQlt q hq)]
  · rw [List.all_eq_true]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    have hqn : q < n := by omega
    obtain ⟨a, b⟩ := hZ q hqn hq
    rw [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, tm_eq hqn hqn]
    exact ⟨a, b⟩
  · exact List.contains_iff_mem.2 hf
  · rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem, hmD, h38D]
    exact Bool.false_ne_true
  · rw [List.all_eq_true]
    intro d hd
    obtain ⟨k, hk, rfl⟩ := (hasBit_dMask DT 32 d).1 ((hmD d).1 hd)
    rw [tm_eq h38 (hDinv k hk).1, ord8_eq hrows hn0 (hrows 38 h38 _ (hDinv k hk).1)]
    exact hord k hk
  · rw [allIn_iff]
    intro i _ hi
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hc : hasBit (dMask DT 32) i = true
    · exact Or.inl (Or.inl (by rw [List.contains_iff_mem, hmD]; exact hc))
    · by_cases hall : ∀ d < n, hasBit (dMask DT 32) d = true → ord8K MT (tmK MT i d) = true
      · right
        rw [htinv 38 h38, tm_eq (hinvlt 38 h38) hi, List.contains_iff_mem, hmD]
        exact (hR i hi).2.2.2.2 (by simpa using hc) hall
      · left
        right
        rw [← Bool.not_eq_true, List.all_eq_true]
        intro hA
        apply hall
        intro d hd hdD
        have := hA d ((hmD d).2 hdD)
        rwa [tm_eq hi hd, ord8_eq hrows hn0 (hrows i hi d hd)] at this

end CFSG.KS.SporSch.LySylP.Table

end
