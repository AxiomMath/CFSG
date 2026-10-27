module

public import Certificates.Data.Kernel.Spor.TBfs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.TBfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.Perm.Native CFSG.Sporadic.Th.Native

@[expose] noncomputable def tbfsRec (n cnt : Nat) (PTS POS PAR LAB : Nat → Nat) : Tree :=
  ⟨Array.ofFn (n := cnt) fun k => UInt32.ofNat (r32 PTS k.val),
    Array.ofFn (n := n) fun z => UInt32.ofNat (r32 POS z.val),
    Array.ofFn (n := cnt) fun k => UInt32.ofNat (r32 PAR k.val),
    Array.ofFn (n := cnt) fun k => UInt32.ofNat (r32 LAB k.val)⟩

@[expose] def LexLt (a b c d : Nat) : Prop := a < c ∨ (a = c ∧ b < d)

theorem lexLtK_iff {a b c d : Nat} : Raw.lexLtK a b c d = true ↔ LexLt a b c d := by
  unfold Raw.lexLtK LexLt
  rw [Raw.Orb.bIf_eq, Raw.Orb.bAnd_eq]
  by_cases h : a < c
  · simp [h]
  · simp [h, Nat.beq_eq]

theorem r32_le (F : Nat → Nat) (i : Nat) : r32 F i ≤ 4294967295 := by
  unfold r32 CFSG.KS.Row.rg
  exact Nat.and_le_right

theorem toNat_r32 (F : Nat → Nat) (i : Nat) : (UInt32.ofNat (r32 F i)).toNat = r32 F i :=
  UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (r32_le F i) (by decide))

structure Hd (n root cnt : Nat) (PTS POS PAR LAB : Nat → Nat) : Prop where
  cnt_pos : 0 < cnt
  cnt_le : cnt ≤ n
  n_lt : n < 4294967295
  root : r32 PTS 0 = root
  par0 : r32 PAR 0 = 0
  lab0 : r32 LAB 0 = 0
  pos : ∀ z < n, r32 POS z = 4294967295 ∨ (r32 POS z < cnt ∧ r32 PTS (r32 POS z) = z)

theorem hd_spec {n root cnt : Nat} {PTS POS PAR LAB : Nat → Nat}
    (h : tbfsHdK n root cnt PTS POS PAR LAB = true) : Hd n root cnt PTS POS PAR LAB := by
  unfold tbfsHdK none32K at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun z hz => ?_⟩
  have := Raw.Orb.allN_iff.1 h7 z hz
  rw [Raw.Orb.strictB_eq, Raw.Orb.bIf_eq] at this
  by_cases e : r32 POS z = 4294967295
  · exact Or.inl e
  · right
    have e' : Nat.beq (r32 POS z) 4294967295 = false :=
      Bool.eq_false_iff.2 fun h => e (Nat.eq_of_beq_eq_true h)
    rw [e'] at this
    simpa [Raw.Orb.bAnd_eq, Nat.blt_eq, Nat.beq_eq] using this

structure Pt (n cnt r : Nat) (L : Nat → Nat → Nat) (LV : Nat → Nat)
    (PTS POS PAR LAB TI : Nat → Nat) (k : Nat) : Prop where
  lt : r32 PTS k < n
  pos : r32 POS (r32 PTS k) = k
  tree : 0 < k → r32 PAR k < k ∧ r32 TI k < r ∧ r32 LAB k = LV (r32 TI k) ∧
    L (LV (r32 TI k)) (r32 PTS (r32 PAR k)) = r32 PTS k ∧
    (k + 1 < cnt → LexLt (r32 PAR k) (r32 TI k) (r32 PAR (k + 1)) (r32 TI (k + 1)))
  close : ∀ t < r, L (LV t) (r32 PTS k) < n ∧ r32 POS (L (LV t) (r32 PTS k)) < cnt ∧
    (r32 POS (L (LV t) (r32 PTS k)) = 0 ∨ ¬ LexLt k t (r32 PAR (r32 POS (L (LV t) (r32 PTS k))))
      (r32 TI (r32 POS (L (LV t) (r32 PTS k)))))

theorem pt_spec {n cnt r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {k : Nat}
    (h : tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true) :
    Pt n cnt r L LV PTS POS PAR LAB TI k := by
  unfold tbfsPtK at h
  rw [Raw.Orb.strictB_eq] at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, ht, hc⟩ := h
  refine ⟨by simpa [Nat.blt_eq] using h1, by simpa [Nat.beq_eq] using h2, fun hk => ?_,
    fun t ht' => ?_⟩
  · have e : Nat.beq k 0 = false :=
      Bool.eq_false_iff.2 fun h => (Nat.pos_iff_ne_zero.1 hk) (Nat.eq_of_beq_eq_true h)
    rw [Raw.Orb.bIf_eq, e, ite_eq_right (by decide), Raw.Orb.strictB_eq, Raw.Orb.strictB_eq] at ht
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Raw.Orb.bIf_eq] at ht
    obtain ⟨a1, a2, a3, a4, a5⟩ := ht
    refine ⟨a1, a2, a3, a4, fun hk1 => ?_⟩
    have hk1' : Nat.succ k < cnt := hk1
    simp only [hk1', ite_true] at a5
    exact lexLtK_iff.1 a5
  · have hq := Raw.Orb.allN_iff.1 hc t ht'
    simp only [Raw.Orb.strictB_eq, Bool.and_eq_true, Nat.blt_eq] at hq
    obtain ⟨a1, a2, a3⟩ := hq
    refine ⟨a1, a2, ?_⟩
    by_cases h0 : r32 POS (L (LV t) (r32 PTS k)) = 0
    · exact Or.inl h0
    · right
      intro hl
      have e : Nat.beq (r32 POS (L (LV t) (r32 PTS k))) 0 = false :=
        Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [Raw.Orb.bIf_eq, e, Raw.Orb.bIf_eq, lexLtK_iff.2 hl] at a3
      exact absurd a3 (by decide)

theorem forIn_list_yield {α β : Type} (xs : List α) (init : β) (f : α → β → Id (ForInStep β))
    (P : Nat → β → Prop)
    (h : ∀ j (hj : j < xs.length), ∀ b, P j b →
      ∃ b', f xs[j] b = pure (ForInStep.yield b') ∧ P (j + 1) b')
    (h0 : P 0 init) : P xs.length (Id.run (forIn xs init f)) := by
  induction xs generalizing init P with
  | nil => simpa using h0
  | cons x xs ih =>
    rw [List.forIn_cons]
    obtain ⟨b', hb, hP⟩ := h 0 (by simp) init h0
    simp only [List.getElem_cons_zero] at hb
    rw [hb]
    have := ih b' (fun j b => P (j + 1) b) (fun j hj b hbj => by
      obtain ⟨b'', e, p⟩ := h (j + 1) (by simp; omega) b hbj
      exact ⟨b'', by simpa using e, p⟩) hP
    simpa using this

theorem forIn_range'_done {β : Type} (n s : Nat) (init : β) (f : Nat → β → Id (ForInStep β))
    (P : Nat → β → Prop) (Q : β → Prop)
    (h : ∀ j < n, ∀ b, P j b → (∃ b', f (s + j) b = pure (ForInStep.yield b') ∧ P (j + 1) b') ∨
      (∃ b', f (s + j) b = pure (ForInStep.done b') ∧ Q b'))
    (hn : ∀ b, P n b → Q b) (h0 : P 0 init) : Q (Id.run (forIn (List.range' s n) init f)) := by
  induction n generalizing s init P with
  | zero => simpa using hn init h0
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    rcases h 0 (by omega) init h0 with ⟨b', hb, hP⟩ | ⟨b', hb, hQ⟩
    · rw [Nat.add_zero] at hb
      rw [hb]
      have := ih (s + 1) b' (fun j b => P (j + 1) b) (fun j hj b hbj => by
        rcases h (j + 1) (by omega) b hbj with ⟨b'', e, p⟩ | ⟨b'', e, q⟩
        · exact Or.inl ⟨b'', by rw [show s + 1 + j = s + (j + 1) by omega]; exact e, p⟩
        · exact Or.inr ⟨b'', by rw [show s + 1 + j = s + (j + 1) by omega]; exact e, q⟩)
        (fun b hb => hn b hb) hP
      simpa using this
    · rw [Nat.add_zero] at hb
      rw [hb]
      simpa using hQ

abbrev St := Table × Table × Table × Table

@[expose] def innerBody (letters : Array Table) (p h l : Nat) (s : St) : Id (ForInStep St) :=
  if (s.1[ap letters[l]! p]! == none32) = true then
    pure (ForInStep.yield (s.1.set! (ap letters[l]! p) (UInt32.ofNat s.2.1.size),
      s.2.1.push (UInt32.ofNat (ap letters[l]! p)), s.2.2.1.push (UInt32.ofNat h),
      s.2.2.2.push (UInt32.ofNat l)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def outerBody (letters : Array Table) (lv : Array Nat) (h : Nat) (s : St) :
    Id (ForInStep St) :=
  if h < s.2.1.size then
    pure (ForInStep.yield (Id.run (forIn lv (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (innerBody letters (ap s.2.1 h) h))))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def initSt (n root : Nat) : St :=
  ((Array.replicate n none32).set! root 0, #[UInt32.ofNat root], #[0], #[0])

theorem treeBFS_eq (n root : Nat) (letters : Array Table) (lv : Array Nat) :
    treeBFS n root letters lv =
      let s := Id.run (forIn (List.range' 0 n) (initSt n root) (outerBody letters lv))
      ⟨s.2.1, s.1, s.2.2.1, s.2.2.2⟩ := by
  unfold treeBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem push_lt {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), Array.getElem_push_lt h, getElem!_pos a i h]

theorem push_eq {α : Type} [Inhabited α] {a : Array α} {x : α} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

theorem set!_get {a : Table} {i j : Nat} {v : UInt32} (_hi : i < a.size) (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by simp; omega), getElem!_pos a j hj]
  by_cases e : i = j
  · subst e
    simp
  · rw [Array.getElem_setIfInBounds_ne hj e]
    simp [e]

theorem ofFn_get {α : Type} [Inhabited α] {c i : Nat} {f : Nat → α} (hi : i < c) :
    (Array.ofFn (n := c) fun k => f k.val)[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem allIn_iff {n : Nat} {p : Nat → Bool} : allIn 0 n p = true ↔ ∀ i < n, p i = true := by
  unfold allIn
  rw [Nat.sub_zero, Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    simpa using h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h ⟨i, hi⟩ _
    simpa using h i hi

theorem none32_toNat :(none32 ()).toNat = 4294967295 := rfl

theorem ofNat_ne_none {x : Nat} (hx : x < 4294967295) : UInt32.ofNat x ≠ none32 () := by
  intro e
  have := congrArg UInt32.toNat e
  rw [UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hx (by decide)), none32_toNat] at this
  omega

structure Rep (n root cnt r : Nat) (L : Nat → Nat → Nat) (LV : Nat → Nat)
    (PTS POS PAR LAB TI : Nat → Nat) : Prop where
  hd : Hd n root cnt PTS POS PAR LAB
  pt : ∀ k < cnt, Pt n cnt r L LV PTS POS PAR LAB TI k

section

variable {n root cnt r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
  {PTS POS PAR LAB TI : Nat → Nat}

theorem lex_trans {a b c d e f : Nat} (h1 : LexLt a b c d) (h2 : LexLt c d e f) : LexLt a b e f := by
  unfold LexLt at *
  omega

theorem Rep.order_lt (R : Rep n root cnt r L LV PTS POS PAR LAB TI) {i i' : Nat} (h0 : 0 < i)
    (hi : i < i') (hi' : i' < cnt) :
    LexLt (r32 PAR i) (r32 TI i) (r32 PAR i') (r32 TI i') := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with a | a
    · exact lex_trans (ih a (by omega)) (((R.pt i' (by omega)).tree (by omega)).2.2.2.2 hi')
    · have e : i = i' := by omega
      subst e
      exact ((R.pt i (by omega)).tree h0).2.2.2.2 hi'

theorem Rep.inj (R : Rep n root cnt r L LV PTS POS PAR LAB TI) {a b : Nat} (ha : a < cnt)
    (hb : b < cnt) (e : r32 PTS a = r32 PTS b) : a = b := by
  rw [← (R.pt a ha).pos, ← (R.pt b hb).pos, e]

theorem Rep.pts_pos (R : Rep n root cnt r L LV PTS POS PAR LAB TI) {z : Nat} (hz : z < n)
    (hk : r32 POS z < cnt) : r32 PTS (r32 POS z) = z := by
  rcases R.hd.pos z hz with e | e
  · have := R.hd.cnt_le
    have := R.hd.n_lt
    omega
  · exact e.2

@[expose] def Inv (n cnt : Nat) (PTS POS PAR LAB TI : Nat → Nat) (h j : Nat) (s : St) : Prop :=
  s.2.1.size ≤ cnt ∧ s.2.2.1.size = s.2.1.size ∧ s.2.2.2.size = s.2.1.size ∧
    (∀ i < s.2.1.size, s.2.1[i]! = UInt32.ofNat (r32 PTS i) ∧
      s.2.2.1[i]! = UInt32.ofNat (r32 PAR i) ∧ s.2.2.2[i]! = UInt32.ofNat (r32 LAB i)) ∧
    s.1.size = n ∧
    (∀ z < n, s.1[z]! = if r32 POS z < s.2.1.size then UInt32.ofNat (r32 POS z) else none32 ()) ∧
    (∀ i < cnt, i < s.2.1.size ↔ (i = 0 ∨ LexLt (r32 PAR i) (r32 TI i) h j))

theorem inv_init (R : Rep n root cnt r L LV PTS POS PAR LAB TI) :
    Inv n cnt PTS POS PAR LAB TI 0 0 (initSt n root) := by
  have hc := R.hd.cnt_pos
  have hcn := R.hd.cnt_le
  have hroot : root < n := by rw [← R.hd.root]; exact (R.pt 0 hc).lt
  have hpr : r32 POS root = 0 := by
    have := (R.pt 0 hc).pos
    rwa [R.hd.root] at this
  refine ⟨by simp [initSt]; omega, rfl, rfl, fun i hi => ?_, by simp [initSt], fun z hz => ?_,
    fun i hi => ?_⟩
  · have : i = 0 := by simp [initSt] at hi; omega
    subst this
    simp [initSt, R.hd.root, R.hd.par0, R.hd.lab0]
  · simp only [initSt, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
    rw [set!_get (by simpa using hroot) (by simpa using hz)]
    by_cases e : root = z
    · subst e
      simp [hpr]
    · rw [ite_eq_right e]
      have hz0 : r32 POS z ≠ 0 := by
        intro h0
        have := R.pts_pos hz (by omega)
        rw [h0, R.hd.root] at this
        exact e this
      rw [ite_eq_right (by omega), getElem!_pos _ z (by simpa using hz)]
      simp
  · simp only [initSt, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
    unfold LexLt
    omega

@[expose] def LvRep (n r : Nat) (L : Nat → Nat → Nat) (LV : Nat → Nat) (letters : Array Table)
    (lv : Array Nat) : Prop :=
  lv.size = r ∧ ∀ t < r, lv[t]! = LV t ∧ LV t < letters.size ∧
    ∀ x < n, ap letters[LV t]! x = L (LV t) x

theorem inner_step (R : Rep n root cnt r L LV PTS POS PAR LAB TI) {letters : Array Table}
    {lv : Array Nat} (hlv : LvRep n r L LV letters lv) {h t : Nat} (hh : h < cnt) (ht : t < r)
    {s : St} (hI : Inv n cnt PTS POS PAR LAB TI h t s) :
    ∃ s', innerBody letters (r32 PTS h) h lv[t]! s = pure (ForInStep.yield s') ∧
      Inv n cnt PTS POS PAR LAB TI h (t + 1) s' ∧ s.2.1.size ≤ s'.2.1.size := by
  obtain ⟨hle, hp, hl, hget, hn, hpos, hch⟩ := hI
  obtain ⟨hlvt, -, hap⟩ := hlv.2 t ht
  have hPh := (R.pt h hh).lt
  obtain ⟨hq, hkq, hor⟩ := (R.pt h hh).close t ht
  have hapq : ap letters[lv[t]!]! (r32 PTS h) = L (LV t) (r32 PTS h) := by
    rw [hlvt]
    exact hap _ hPh
  have hcn := R.hd.cnt_le
  have hnl := R.hd.n_lt
  generalize hqdef : L (LV t) (r32 PTS h) = q at hq hkq hor hapq
  generalize hkdef : r32 POS q = kq at hkq hor
  have hPk : r32 PTS kq = q := by rw [← hkdef]; exact R.pts_pos hq (by omega)
  have hpair : ∀ i < cnt, 0 < i → r32 PAR i = h → r32 TI i = t → i = kq := by
    intro i hi h0 e1 e2
    obtain ⟨-, -, -, e, -⟩ := (R.pt i hi).tree h0
    rw [e1, e2, hqdef] at e
    rw [← hkdef, e]
    exact ((R.pt i hi).pos).symm
  have hmove : ∀ i < cnt, (i = 0 ∨ LexLt (r32 PAR i) (r32 TI i) h (t + 1)) ↔
      ((i = 0 ∨ LexLt (r32 PAR i) (r32 TI i) h t) ∨
        (0 < i ∧ r32 PAR i = h ∧ r32 TI i = t)) := by
    intro i _
    unfold LexLt
    omega
  have hsn : q < s.1.size := by rw [hn]; exact hq
  unfold innerBody
  rw [hapq, hpos q hq, hkdef]
  by_cases hnew : 0 < kq ∧ r32 PAR kq = h ∧ r32 TI kq = t
  · obtain ⟨hk0, hpk, htk⟩ := hnew
    have hks : ¬ kq < s.2.1.size := by
      rw [hch kq hkq]
      rintro (e | e)
      · omega
      · rw [hpk, htk] at e
        unfold LexLt at e
        omega
    have hkm : kq = s.2.1.size := by
      refine Nat.le_antisymm (Nat.le_of_not_lt fun hlt => ?_) (by omega)
      have hm0 : 0 < s.2.1.size := (hch 0 R.hd.cnt_pos).2 (Or.inl rfl) |> fun h => by omega
      have hns : ¬ (s.2.1.size = 0 ∨ LexLt (r32 PAR s.2.1.size) (r32 TI s.2.1.size) h t) := by
        rw [← hch s.2.1.size (by omega)]
        exact Nat.lt_irrefl _
      have := R.order_lt hm0 hlt hkq
      rw [hpk, htk] at this
      exact hns (Or.inr this)
    have hlab : r32 LAB kq = LV t := by
      rw [((R.pt kq hkq).tree hk0).2.2.1, htk]
    rw [ite_eq_right hks]
    simp only [beq_self_eq_true, ite_true]
    refine ⟨_, rfl, ⟨by simp; omega, by simp [hp], by simp [hl], fun i hi => ?_, by simp [hn],
      fun z hz => ?_, fun i hi => ?_⟩, by simp⟩
    · simp only [Array.size_push] at hi
      rcases Nat.lt_or_ge i s.2.1.size with a | a
      · rw [push_lt a, push_lt (by omega : i < s.2.2.1.size),
          push_lt (by omega : i < s.2.2.2.size)]
        exact hget i a
      · have e : i = s.2.1.size := by omega
        subst e
        have e1 : (s.2.2.1.push (UInt32.ofNat h))[s.2.1.size]! = UInt32.ofNat h := by
          rw [← hp]; exact push_eq
        have e2 : (s.2.2.2.push (UInt32.ofNat lv[t]!))[s.2.1.size]! = UInt32.ofNat lv[t]! := by
          rw [← hl]; exact push_eq
        refine ⟨?_, ?_, ?_⟩
        · rw [push_eq, ← hkm, hPk]
        · rw [e1, ← hkm, hpk]
        · rw [e2, ← hkm, hlab, hlvt]
    · rw [set!_get hsn (by omega), Array.size_push]
      by_cases e : q = z
      · subst e
        rw [ite_eq_left_iff.2 (fun h => absurd rfl h), hkdef, ← hkm]
        simp
      · rw [ite_eq_right e, hpos z hz]
        have hne : r32 POS z ≠ s.2.1.size := by
          intro e'
          apply e
          rw [← R.pts_pos hz (by omega), e', ← hkm, hPk]
        by_cases hz' : r32 POS z < s.2.1.size
        · rw [ite_eq_left hz', ite_eq_left (by omega)]
        · rw [ite_eq_right hz', ite_eq_right (by omega)]
    · simp only [Array.size_push]
      rw [hmove i hi, ← hch i hi]
      constructor
      · intro hlt
        rcases Nat.lt_or_ge i s.2.1.size with a | a
        · exact Or.inl a
        · have e : i = s.2.1.size := by omega
          subst e
          exact Or.inr ⟨by omega, by rw [← hkm]; exact hpk, by rw [← hkm]; exact htk⟩
      · rintro (a | ⟨a0, a1, a2⟩)
        · omega
        · have := hpair i hi a0 a1 a2
          omega
  ·
    have hks : kq < s.2.1.size := by
      rw [hch kq hkq]
      rcases hor with e | e
      · exact Or.inl e
      · by_cases h0 : kq = 0
        · exact Or.inl h0
        · right
          unfold LexLt at e ⊢
          have : ¬ (r32 PAR kq = h ∧ r32 TI kq = t) := fun e' => hnew ⟨by omega, e'.1, e'.2⟩
          omega
    have hne : (UInt32.ofNat kq == none32 ()) = false := by
      rw [beq_eq_false_iff_ne]
      exact ofNat_ne_none (by omega)
    rw [ite_eq_left hks, hne]
    refine ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), rfl,
      ⟨hle, hp, hl, hget, hn, hpos, fun i hi => ?_⟩, Nat.le_refl _⟩
    rw [hmove i hi, ← hch i hi]
    constructor
    · exact Or.inl
    · rintro (a | ⟨a0, a1, a2⟩)
      · exact a
      · rw [hpair i hi a0 a1 a2]
        exact hks

theorem inner_spec (R : Rep n root cnt r L LV PTS POS PAR LAB TI) {letters : Array Table}
    {lv : Array Nat} (hlv : LvRep n r L LV letters lv) {h : Nat} (hh : h < cnt) {s : St}
    (hI : Inv n cnt PTS POS PAR LAB TI h 0 s) (hhs : h < s.2.1.size) :
    Inv n cnt PTS POS PAR LAB TI (h + 1) 0
      (Id.run (forIn lv (s.1, s.2.1, s.2.2.1, s.2.2.2) (innerBody letters (ap s.2.1 h) h))) := by
  have hT : ap s.2.1 h = r32 PTS h := by
    unfold ap
    rw [(hI.2.2.2.1 h hhs).1, toNat_r32]
  rw [hT, ← Array.forIn_toList]
  have hsz : lv.toList.length = r := by rw [Array.length_toList]; exact hlv.1
  have := forIn_list_yield lv.toList (s.1, s.2.1, s.2.2.1, s.2.2.2)
    (innerBody letters (r32 PTS h) h) (fun j s' => Inv n cnt PTS POS PAR LAB TI h j s')
    (fun j hj s' hP => by
      have hj' : j < r := by omega
      obtain ⟨s'', e, hI', -⟩ := inner_step R hlv hh hj' hP
      refine ⟨s'', ?_, hI'⟩
      rw [Array.getElem_toList, ← getElem!_pos lv j (by rw [hlv.1]; exact hj')]
      exact e) hI
  rw [hsz] at this
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := this
  refine ⟨a1, a2, a3, a4, a5, a6, fun i hi => ?_⟩
  rw [a7 i hi]
  have hlab : 0 < i → r32 TI i < r := fun h0 => ((R.pt i hi).tree h0).2.1
  unfold LexLt
  constructor
  · rintro (e | e)
    · exact Or.inl e
    · right
      omega
  · rintro (e | e)
    · exact Or.inl e
    · by_cases h0 : i = 0
      · exact Or.inl h0
      · right
        have := hlab (by omega)
        omega

theorem outer_spec (R : Rep n root cnt r L LV PTS POS PAR LAB TI) {letters : Array Table}
    {lv : Array Nat} (hlv : LvRep n r L LV letters lv) :
    Inv n cnt PTS POS PAR LAB TI cnt 0
      (Id.run (forIn (List.range' 0 n) (initSt n root) (outerBody letters lv))) := by
  refine forIn_range'_done n 0 (initSt n root) (outerBody letters lv)
    (fun h s => h ≤ cnt ∧ Inv n cnt PTS POS PAR LAB TI h 0 s) (Inv n cnt PTS POS PAR LAB TI cnt 0)
    (fun h hh s hP => ?_) (fun s hP => ?_) ⟨Nat.zero_le _, inv_init R⟩
  · obtain ⟨hhc, hI⟩ := hP
    rw [Nat.zero_add]
    rcases Nat.lt_or_ge h cnt with a | a
    · have hhs : h < s.2.1.size := by
        rw [hI.2.2.2.2.2.2 h a]
        by_cases h0 : h = 0
        · exact Or.inl h0
        · right
          left
          exact ((R.pt h a).tree (by omega)).1
      exact Or.inl ⟨_, by simp [outerBody, hhs], by omega, inner_spec R hlv a hI hhs⟩
    · have e : h = cnt := by omega
      subst e
      have hns : ¬ h < s.2.1.size := by have := hI.1; omega
      exact Or.inr ⟨_, by simp [outerBody, hns], hI⟩
  · have := R.hd.cnt_le
    have e : n = cnt := by have := hP.1; omega
    exact Eq.mp (by rw [e]) hP.2

end

theorem ap_ofFn {c i : Nat} {F : Nat → Nat} (hi : i < c) :
    ap (Array.ofFn (n := c) fun k => UInt32.ofNat (r32 F k.val)) i = r32 F i := by
  unfold ap
  rw [ofFn_get (f := fun k => UInt32.ofNat (r32 F k)) hi, toNat_r32]

theorem tbfs_of_rep {n root cnt r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {letters : Array Table} {lv : Array Nat}
    (hlv : LvRep n r L LV letters lv) (R : Rep n root cnt r L LV PTS POS PAR LAB TI) :
    treeBFS n root letters lv = tbfsRec n cnt PTS POS PAR LAB ∧
      treeOK n root (tbfsRec n cnt PTS POS PAR LAB) letters lv = true := by
  have hc := R.hd.cnt_pos
  have hcn := R.hd.cnt_le
  have hnl := R.hd.n_lt
  refine ⟨?_, ?_⟩
  · have hO := outer_spec R hlv
    rw [treeBFS_eq]
    generalize Id.run (forIn (List.range' 0 n) (initSt n root) (outerBody letters lv)) = s at hO
    obtain ⟨hle, hp, hl, hget, hn, hpos, hch⟩ := hO
    have hsz : s.2.1.size = cnt := by
      have := (hch (cnt - 1) (by omega)).2 (by
        by_cases h0 : cnt - 1 = 0
        · exact Or.inl h0
        · right
          left
          have := ((R.pt (cnt - 1) (by omega)).tree (by omega)).1
          omega)
      omega
    have ext : ∀ (a : Table) (c : Nat) (f : Nat → UInt32), a.size = c → (∀ i < c, a[i]! = f i) →
        a = Array.ofFn (n := c) fun i => f i.val := fun a c f ha hf => by
      apply Array.ext
      · simp [ha]
      · intro i h1 h2
        rw [Array.getElem_ofFn, ← getElem!_pos a i h1, hf i (by omega)]
    unfold tbfsRec
    simp only
    rw [ext s.2.1 cnt _ hsz fun i hi => (hget i (by omega)).1,
      ext s.2.2.1 cnt _ (by omega) fun i hi => (hget i (by omega)).2.1,
      ext s.2.2.2 cnt _ (by omega) fun i hi => (hget i (by omega)).2.2,
      ext s.1 n (fun z => UInt32.ofNat (r32 POS z)) hn fun z hz => ?_]
    rw [hpos z hz, hsz]
    by_cases e : r32 POS z < cnt
    · rw [ite_eq_left e]
    · rw [ite_eq_right e]
      rcases R.hd.pos z hz with e' | e'
      · rw [e']
        rfl
      · exact absurd e'.1 e
  · unfold Perm.Native.treeOK treeAt
    simp only [tbfsRec, Array.size_ofFn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨hc, by rw [ap_ofFn hc, R.hd.root]⟩, ?_⟩
    rw [allIn_iff]
    intro k hk
    have P := R.pt k hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    simp only [ap_ofFn hk, ap_ofFn P.lt, P.pos]
    refine ⟨⟨⟨decide_eq_true P.lt, trivial⟩, ?_⟩, ?_⟩
    · rw [Array.all_eq_true]
      intro j hj
      have hj' : j < r := by rw [← hlv.1]; exact hj
      obtain ⟨hlvt, -, hap⟩ := hlv.2 j hj'
      have e : lv[j] = LV j := by rw [← getElem!_pos lv j hj, hlvt]
      obtain ⟨hq, hkq, -⟩ := P.close j hj'
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      simp only [e, hap _ P.lt, ap_ofFn hq, ap_ofFn hkq, R.pts_pos hq hkq]
      exact ⟨hkq, trivial⟩
    · by_cases h0 : k = 0
      · exact Or.inl h0
      · right
        obtain ⟨a1, a2, a3, a4, -⟩ := P.tree (by omega)
        obtain ⟨hlvt, -, hap⟩ := hlv.2 _ a2
        have hpa : r32 PAR k < cnt := by omega
        rw [ap_ofFn hpa, a3, hap _ (R.pt _ hpa).lt, a4]
        refine ⟨⟨decide_eq_true a1, ?_⟩, rfl⟩
        have hs : r32 TI k < lv.size := by rw [hlv.1]; exact a2
        rw [Array.contains_iff_mem, ← hlvt, getElem!_pos lv _ hs]
        exact Array.getElem_mem hs

theorem tbfsK_sound {n root cnt r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {letters : Array Table} {lv : Array Nat}
    (hlv : lv.size = r ∧ ∀ t < r, lv[t]! = LV t ∧ LV t < letters.size ∧
      ∀ x < n, ap letters[LV t]! x = L (LV t) x)
    (hh : tbfsHdK n root cnt PTS POS PAR LAB = true)
    (hp : ∀ k < cnt, tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true) :
    treeBFS n root letters lv = tbfsRec n cnt PTS POS PAR LAB ∧
      treeOK n root (tbfsRec n cnt PTS POS PAR LAB) letters lv = true :=
  tbfs_of_rep hlv ⟨hd_spec hh, fun k hk => pt_spec (hp k hk)⟩

end CFSG.KS.TBfs

end
