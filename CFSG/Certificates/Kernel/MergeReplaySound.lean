module

public import Certificates.Data.Kernel.MergeReplay
public import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public import CFSG.Sporadic.Co1Block.CentCheck

public section

namespace CFSG.KC.MergeR

open CFSG.Sporadic.Co1Block.Native CFSG.KC.Enum CFSG.KS CFSG.KC.Pack

abbrev St := Array Nat × Array Nat × Array (Nat × Nat) × Array (Nat × Nat × Nat)

@[expose] def innerA (n : Nat) (G : Array (Array Nat)) (u v : Nat) (s : St) (i : Nat) : St :=
  if ufFind s.1 n (G[i]!)[u]! != ufFind s.1 n (G[i]!)[v]! then
    if s.2.1[ufFind s.1 n (G[i]!)[u]!]! < s.2.1[ufFind s.1 n (G[i]!)[v]!]! then
      (s.1.set! (ufFind s.1 n (G[i]!)[u]!) (ufFind s.1 n (G[i]!)[v]!),
        s.2.1.set! (ufFind s.1 n (G[i]!)[v]!)
          (s.2.1[ufFind s.1 n (G[i]!)[u]!]! + s.2.1[ufFind s.1 n (G[i]!)[v]!]!),
        s.2.2.1.push ((G[i]!)[u]!, (G[i]!)[v]!), s.2.2.2.push (i, u, v))
    else
      (s.1.set! (ufFind s.1 n (G[i]!)[v]!) (ufFind s.1 n (G[i]!)[u]!),
        s.2.1.set! (ufFind s.1 n (G[i]!)[u]!)
          (s.2.1[ufFind s.1 n (G[i]!)[u]!]! + s.2.1[ufFind s.1 n (G[i]!)[v]!]!),
        s.2.2.1.push ((G[i]!)[u]!, (G[i]!)[v]!), s.2.2.2.push (i, u, v))
  else s

theorem forIn_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (hf : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, hf]
    exact ih _

theorem step_eq (n : Nat) (G : Array (Array Nat)) (st : St) (h : Nat) :
    mergeSearchStep n G st h =
      if h < st.2.2.1.size then
        (List.range G.size).foldl (innerA n G (st.2.2.1[h]!).1 (st.2.2.1[h]!).2) st
      else st := by
  obtain ⟨par, sz, queue, out⟩ := st
  by_cases hh : h < queue.size
  · rw [ite_eq_left hh]
    generalize hq : queue[h]! = p
    obtain ⟨u, v⟩ := p
    simp only [mergeSearchStep, hh, ↓reduceIte, hq]
    rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_yield _ _ _ (fun s i => innerA n G u v s i)]
    · simp [Std.Legacy.Range.size, List.range_eq_range']
    · intro i s
      obtain ⟨p, z, q, o⟩ := s
      simp only [innerA]
      split_ifs <;> rfl
  · simp [mergeSearchStep, hh]

theorem set_get {α : Type} [Inhabited α] {a : Array α} {i j : Nat} {v : α} (hi : i < a.size) :
    (a.set! i v)[j]! = if j = i then v else a[j]! := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set! i v).size := by simpa using hj
    rw [getElem!_pos _ j hj', getElem!_pos a j hj]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
  · have hj' : ¬ j < (a.set! i v).size := by simpa using hj
    have hij : j ≠ i := by omega
    rw [getElem!_neg _ j hj', getElem!_neg a j hj, ite_eq_right hij]

theorem get_of_toList {α : Type} [Inhabited α] {a : Array α} {l : List α} (e : a.toList = l)
    {i : Nat} (hi : i < l.length) : a[i]! = l[i] := by
  have hs : i < a.size := by rw [← Array.length_toList, e]; exact hi
  rw [getElem!_pos a i hs, ← Array.getElem_toList]
  simp only [e]

@[expose] noncomputable def recT (w m Lp j : Nat) : Nat × Nat × Nat :=
  (recF w m Lp j (nat_lit 0), recF w m Lp j (nat_lit 1), recF w m Lp j (nat_lit 2))

theorem recT_eq (w m Lp j : Nat) :
    recT w m Lp j = (pg w m Lp (3 * j), pg w m Lp (3 * j + 1), pg w m Lp (3 * j + 2)) := rfl

@[expose] def img (G : Array (Array Nat)) (r : Nat × Nat × Nat) : Nat × Nat :=
  ((G[r.1]!)[r.2.1]!, (G[r.1]!)[r.2.2]!)

@[expose] def Rel (n w nw : Nat) (G : Array (Array Nat)) (b x Lp : Nat) (s : St) (st : Nat) :
    Prop :=
  st % 2 = 0 ∧ st < 2 ^ (33 + nw + nw) ∧ s.1.size = n ∧ s.2.1.size = n ∧
    (∀ j, s.1[j]! = Nat.land (Nat.shiftRight st (parOff w nw j)) (2 ^ w - 1)) ∧
    (∀ j < n, s.2.1[j]! = Nat.land (Nat.shiftRight st (szOff w j)) (2 ^ w - 1)) ∧
    s.2.2.2.toList = (List.range (kOf st)).map (recT w (2 ^ w - 1) Lp) ∧
    s.2.2.1.toList = (b, x) :: s.2.2.2.toList.map (img G)

theorem kOf_eq (st : Nat) : kOf st = Nat.land (Nat.shiftRight st 1) (2 ^ 32 - 1) := rfl

theorem parOff_eq (w nw j : Nat) : parOff w nw j = 33 + nw + w * j := rfl

theorem szOff_eq (w j : Nat) : szOff w j = 33 + w * j := rfl

theorem land_one (st : Nat) : Nat.land st (nat_lit 1) = st % 2 := Nat.and_one_is_mod st

theorem mod2_eq (st : Nat) : st % 2 = Nat.land (Nat.shiftRight st 0) (2 ^ 1 - 1) := by
  rw [fld_eq]
  simp

theorem mul_lt_le {w j n : Nat} (h : j < n) : w * j + w ≤ w * n := by
  have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
  rwa [Nat.mul_succ] at this

theorem par_disj {w nw i j : Nat} (h : i ≠ j) :
    parOff w nw i + w ≤ parOff w nw j ∨ parOff w nw j + w ≤ parOff w nw i := by
  rw [parOff_eq, parOff_eq]
  rcases disj (w := w) h with h | h <;> [left; right] <;> omega

theorem sz_disj {w i j : Nat} (h : i ≠ j) :
    szOff w i + w ≤ szOff w j ∨ szOff w j + w ≤ szOff w i := by
  rw [szOff_eq, szOff_eq]
  rcases disj (w := w) h with h | h <;> [left; right] <;> omega

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem nif_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem band_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem ufFind_eq {w nw : Nat} {par : Array Nat} {st : Nat}
    (hp : ∀ j, par[j]! = Nat.land (Nat.shiftRight st (parOff w nw j)) (2 ^ w - 1)) :
    ∀ fuel x, ufFind par fuel x = ufK w (2 ^ w - 1) nw st fuel x
  | 0, _ => rfl
  | fuel + 1, x => by
    change _ = strictN (Nat.land (Nat.shiftRight st (parOff w nw x)) (2 ^ w - 1))
      (fun p => Bool.rec (motive := fun _ => Nat) (ufK w (2 ^ w - 1) nw st fuel p) x (Nat.beq p x))
    rw [strictN_eq, ← hp x, ufFind]
    by_cases hx : par[x]! = x
    · rw [hx, Nat.beq_refl]
      simp
    · rw [beq_false hx]
      simp only [beq_iff_eq, hx, ↓reduceIte]
      exact ufFind_eq hp fuel _

theorem rel_write {n w nw : Nat} {G : Array (Array Nat)} {b x Lp : Nat} {s : St} {st : Nat}
    (hnw : nw = n * w) (hr : Rel n w nw G b x Lp s st) {p q q' val i u v : Nat} (hp : p < n)
    (hq : q < 2 ^ w) (hq' : q' < n) (hval : val < 2 ^ w) (hk : kOf st + 1 < 2 ^ 32)
    (hrec : recT w (2 ^ w - 1) Lp (kOf st) = (i, u, v)) :
    Rel n w nw G b x Lp
      (s.1.set! p q, s.2.1.set! q' val, s.2.2.1.push ((G[i]!)[u]!, (G[i]!)[v]!),
        s.2.2.2.push (i, u, v))
      (setO (setO (setO st 1 (2 ^ 32 - 1) (kOf st + 1)) (parOff w nw p) (2 ^ w - 1) q)
        (szOff w q') (2 ^ w - 1) val) := by
  obtain ⟨h0, hT, hs1, hs2, hP, hS, hout, hque⟩ := hr
  have hwp := mul_lt_le (w := w) hp
  have hwq := mul_lt_le (w := w) hq'
  have hnw' : nw = w * n := by rw [hnw, Nat.mul_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mod2_eq, setO_other hval (by rw [szOff_eq]; omega),
      setO_other hq (by rw [parOff_eq]; omega), setO_other hk (by omega), ← mod2_eq]
    exact h0
  · refine setO_lt (setO_lt (setO_lt hT hk (by omega)) hq (by rw [parOff_eq]; omega)) hval
      (by rw [szOff_eq]; omega)
  · simp [hs1]
  · simp [hs2]
  · intro j
    rw [setO_other hval (by rw [szOff_eq, parOff_eq]; omega), set_get (by rw [hs1]; exact hp)]
    by_cases hj : j = p
    · subst hj
      rw [ite_eq_left rfl, setO_get hq]
    · rw [ite_eq_right hj, setO_other hq (par_disj hj),
        setO_other hk (by rw [parOff_eq]; omega), hP j]
  · intro j hj
    rw [set_get (by rw [hs2]; exact hq')]
    by_cases hjq : j = q'
    · subst hjq
      rw [ite_eq_left rfl, setO_get hval]
    · have hwj := mul_lt_le (w := w) hj
      rw [ite_eq_right hjq, setO_other hval (sz_disj hjq),
        setO_other hq (by rw [szOff_eq, parOff_eq]; omega),
        setO_other hk (by rw [szOff_eq]; omega), hS j hj]
  · have hk' : kOf (setO (setO (setO st 1 (2 ^ 32 - 1) (kOf st + 1)) (parOff w nw p) (2 ^ w - 1) q)
        (szOff w q') (2 ^ w - 1) val) = kOf st + 1 := by
      rw [kOf_eq, setO_other hval (by rw [szOff_eq]; omega),
        setO_other hq (by rw [parOff_eq]; omega), setO_get hk]
    rw [hk', Array.toList_push, hout, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil, hrec]
  · rw [Array.toList_push, Array.toList_push, hque, List.map_append]
    rfl

section Gen

variable {n w nw cnt Lp : Nat} {Gp : Nat → Nat} {G : Array (Array Nat)} {b x : Nat}

theorem genK_fail {u v i st : Nat} (h : st % 2 = 1) :
    genK n w (2 ^ w - 1) nw cnt Lp Gp u v i st = st := by
  unfold genK
  rw [land_one, h]
  rfl

theorem genK_rel (hnw : nw = n * w) (hn : n < 2 ^ w) (hcnt : cnt < 2 ^ 32)
    {s : St} {st u v i : Nat} (hr : Rel n w nw G b x Lp s st) (hu : u < n) (hv : v < n)
    (hGp : ∀ y < n, (G[i]!)[y]! = pg w (2 ^ w - 1) (Gp i) y)
    (hg : genK n w (2 ^ w - 1) nw cnt Lp Gp u v i st % 2 = 0) :
    Rel n w nw G b x Lp (innerA n G u v s i) (genK n w (2 ^ w - 1) nw cnt Lp Gp u v i st) := by
  have h0 := hr.1
  have hP := hr.2.2.2.2.1
  have hS := hr.2.2.2.2.2.1
  have hfail : Nat.beq (Nat.land st (nat_lit 1)) (nat_lit 1) = false := by
    rw [land_one, h0]
    rfl
  unfold genK at hg ⊢
  rw [hfail] at hg ⊢
  dsimp only at hg ⊢
  simp only [strictN_eq] at hg ⊢
  rw [← hGp u hu, ← hGp v hv, ← ufFind_eq hP, ← ufFind_eq hP] at hg ⊢
  unfold innerA
  generalize ufFind s.1 n (G[i]!)[u]! = ra at hg ⊢
  generalize ufFind s.1 n (G[i]!)[v]! = rc at hg ⊢
  by_cases hrr : ra = rc
  · subst hrr
    rw [Nat.beq_refl] at hg ⊢
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact hr
  · rw [beq_false hrr] at hg ⊢
    have hne : (ra != rc) = true := by simpa using hrr
    rw [ite_eq_left hne]
    dsimp only at hg ⊢
    unfold unionK at hg ⊢
    simp only [strictN_eq, nif_eq, band_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
      Nat.ble_eq] at hg ⊢
    split at hg
    next h1 =>
      rw [ite_eq_left h1]
      obtain ⟨hra, hrc, hk, hr0, hr1, hr2⟩ := h1
      have hrec : recT w (2 ^ w - 1) Lp (kOf st) = (i, u, v) := by
        rw [recT, hr0, hr1, hr2]
      have hk1 : kOf st + 1 < 2 ^ 32 := by omega
      rw [← hS ra hra, ← hS rc hrc] at hg ⊢
      split at hg
      next h2 =>
        rw [ite_eq_left h2]
        have hsum : Nat.add s.2.1[ra]! s.2.1[rc]! < 2 ^ w := by
          have := Nat.two_pow_pos w
          change s.2.1[ra]! + s.2.1[rc]! ≤ 2 ^ w - 1 at h2
          change s.2.1[ra]! + s.2.1[rc]! < 2 ^ w
          omega
        by_cases h3 : s.2.1[ra]! < s.2.1[rc]!
        · simp only [h3, ↓reduceIte]
          exact rel_write hnw hr hra (by omega) hrc hsum hk1 hrec
        · simp only [h3, ↓reduceIte]
          exact rel_write hnw hr hrc (by omega) hra hsum hk1 hrec
      next => exact absurd hg (by decide)
    next => exact absurd hg (by decide)

theorem genK_foldl_fail {u v : Nat} :
    ∀ (l : List Nat) (t : Nat), t % 2 = 1 →
      l.foldl (fun t i => genK n w (2 ^ w - 1) nw cnt Lp Gp u v i t) t = t
  | [], _, _ => rfl
  | i :: l, t, h => by
    rw [List.foldl_cons, genK_fail h]
    exact genK_foldl_fail l t h

theorem genK_fold (hnw : nw = n * w) (hn : n < 2 ^ w) (hcnt : cnt < 2 ^ 32) {nG : Nat}
    (hGp : ∀ i < nG, ∀ y < n, (G[i]!)[y]! = pg w (2 ^ w - 1) (Gp i) y) {u v : Nat}
    (hu : u < n) (hv : v < n) :
    ∀ (l : List Nat) (s : St) (st : Nat), (∀ i ∈ l, i < nG) → Rel n w nw G b x Lp s st →
      (l.foldl (fun t i => genK n w (2 ^ w - 1) nw cnt Lp Gp u v i t) st) % 2 = 0 →
      Rel n w nw G b x Lp (l.foldl (innerA n G u v) s)
        (l.foldl (fun t i => genK n w (2 ^ w - 1) nw cnt Lp Gp u v i t) st)
  | [], _, _, _, hr, _ => hr
  | i :: l, s, st, hl, hr, hg => by
    simp only [List.foldl_cons] at hg ⊢
    have hi := hl i List.mem_cons_self
    have hgi : genK n w (2 ^ w - 1) nw cnt Lp Gp u v i st % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (genK n w (2 ^ w - 1) nw cnt Lp Gp u v i st) with h | h
      · exact h
      · rw [genK_foldl_fail l _ h] at hg
        omega
    exact genK_fold hnw hn hcnt hGp hu hv l _ _ (fun j hj => hl j (List.mem_cons_of_mem i hj))
      (genK_rel hnw hn hcnt hr hu hv (hGp i hi) hgi) hg

theorem procK_rel (hnw : nw = n * w) (hn : n < 2 ^ w) (hcnt : cnt < 2 ^ 32) {nG : Nat}
    (hGs : G.size = nG) (hGp : ∀ i < nG, ∀ y < n, (G[i]!)[y]! = pg w (2 ^ w - 1) (Gp i) y)
    {u v : Nat} {s : St} {st : Nat} (hr : Rel n w nw G b x Lp s st)
    (hg : procK n w (2 ^ w - 1) nw nG cnt Lp Gp u v st % 2 = 0) :
    Rel n w nw G b x Lp ((List.range G.size).foldl (innerA n G u v) s)
      (procK n w (2 ^ w - 1) nw nG cnt Lp Gp u v st) := by
  unfold procK at hg ⊢
  simp only [nif_eq, band_eq, Bool.and_eq_true, Nat.blt_eq] at hg ⊢
  split at hg
  next h =>
    rw [ite_eq_left h]
    rw [foldUp_eq] at hg ⊢
    rw [hGs]
    exact genK_fold hnw hn hcnt hGp h.1 h.2 _ s st (fun i hi => List.mem_range.1 hi) hr hg
  next => exact absurd hg (by decide)

end Gen

section Step

variable {n w nw nG cnt Lp : Nat} {Gp : Nat → Nat} {G : Array (Array Nat)} {b x : Nat}

theorem stepK_fail {h st : Nat} (hs : st % 2 = 1) :
    stepK n w (2 ^ w - 1) nw nG cnt Lp Gp b x h st = st := by
  unfold stepK
  rw [land_one, hs]
  rfl

theorem stepK_rel (hnw : nw = n * w) (hn : n < 2 ^ w) (hcnt : cnt < 2 ^ 32)
    (hGs : G.size = nG) (hGp : ∀ i < nG, ∀ y < n, (G[i]!)[y]! = pg w (2 ^ w - 1) (Gp i) y)
    {s : St} {st h : Nat} (hr : Rel n w nw G b x Lp s st)
    (hg : stepK n w (2 ^ w - 1) nw nG cnt Lp Gp b x h st % 2 = 0) :
    Rel n w nw G b x Lp (mergeSearchStep n G s h)
      (stepK n w (2 ^ w - 1) nw nG cnt Lp Gp b x h st) := by
  have h0 := hr.1
  have hout := hr.2.2.2.2.2.2.1
  have hque := hr.2.2.2.2.2.2.2
  have hsize : s.2.2.1.size = Nat.succ (kOf st) := by
    rw [← Array.length_toList, hque, List.length_cons, List.length_map, hout, List.length_map,
      List.length_range]
  have hfail : Nat.beq (Nat.land st (nat_lit 1)) (nat_lit 1) = false := by
    rw [land_one, h0]
    rfl
  rw [step_eq, hsize]
  unfold stepK at hg ⊢
  rw [hfail] at hg ⊢
  dsimp only at hg ⊢
  simp only [strictN_eq, nif_eq, band_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hg ⊢
  split at hg
  next hh =>
    simp only [hh, ↓reduceIte]
    have hlen : h < ((b, x) :: s.2.2.2.toList.map (img G)).length := by
      rw [List.length_cons, List.length_map, hout, List.length_map, List.length_range]
      exact hh
    rw [get_of_toList hque hlen]
    split at hg
    next hz =>
      subst hz
      simp only [↓reduceIte, List.getElem_cons_zero]
      exact procK_rel hnw hn hcnt hGs hGp hr hg
    next hz =>
      rw [ite_eq_right hz]
      obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := ⟨h - 1, by omega⟩
      rw [show Nat.sub (j + 1) 1 = j from rfl] at hg ⊢
      split at hg
      next hc =>
        rw [ite_eq_left hc]
        have hj : j < (s.2.2.2.toList.map (img G)).length := by
          simp only [List.length_cons] at hlen
          omega
        rw [List.getElem_cons_succ, List.getElem_map]
        simp only [hout, List.getElem_map, List.getElem_range]
        rw [img, recT]
        dsimp only
        rw [hGp _ hc.1 _ hc.2.1, hGp _ hc.1 _ hc.2.2]
        exact procK_rel hnw hn hcnt hGs hGp hr hg
      next => exact absurd hg (by decide)
  next hh =>
    simp only [hh, ↓reduceIte]
    exact hr

theorem stepK_foldl_fail :
    ∀ (l : List Nat) (t : Nat), t % 2 = 1 →
      l.foldl (fun t h => stepK n w (2 ^ w - 1) nw nG cnt Lp Gp b x h t) t = t
  | [], _, _ => rfl
  | i :: l, t, h => by
    rw [List.foldl_cons, stepK_fail h]
    exact stepK_foldl_fail l t h

theorem stepK_fold (hnw : nw = n * w) (hn : n < 2 ^ w) (hcnt : cnt < 2 ^ 32)
    (hGs : G.size = nG) (hGp : ∀ i < nG, ∀ y < n, (G[i]!)[y]! = pg w (2 ^ w - 1) (Gp i) y) :
    ∀ (l : List Nat) (s : St) (st : Nat), Rel n w nw G b x Lp s st →
      (l.foldl (fun t h => stepK n w (2 ^ w - 1) nw nG cnt Lp Gp b x h t) st) % 2 = 0 →
      Rel n w nw G b x Lp (l.foldl (mergeSearchStep n G) s)
        (l.foldl (fun t h => stepK n w (2 ^ w - 1) nw nG cnt Lp Gp b x h t) st)
  | [], _, _, hr, _ => hr
  | h :: l, s, st, hr, hg => by
    simp only [List.foldl_cons] at hg ⊢
    have hgi : stepK n w (2 ^ w - 1) nw nG cnt Lp Gp b x h st % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (stepK n w (2 ^ w - 1) nw nG cnt Lp Gp b x h st) with
        e | e
      · exact e
      · rw [stepK_foldl_fail l _ e] at hg
        omega
    exact stepK_fold hnw hn hcnt hGs hGp l _ _ (stepK_rel hnw hn hcnt hGs hGp hr hgi) hg

end Step

theorem fld_zero (o r : Nat) : Nat.land (Nat.shiftRight 0 o) (2 ^ r - 1) = 0 := by
  rw [fld_eq]
  simp

theorem init_inv {n w : Nat} (hn : n < 2 ^ w) : ∀ j ≤ n,
    (List.range j).foldl (fun s i => setO (setO s (szOff w i) (2 ^ w - 1) 1)
        (parOff w (n * w) i) (2 ^ w - 1) i) 0 < 2 ^ (33 + n * w + n * w) ∧
      (List.range j).foldl (fun s i => setO (setO s (szOff w i) (2 ^ w - 1) 1)
        (parOff w (n * w) i) (2 ^ w - 1) i) 0 % 2 = 0 ∧
      kOf ((List.range j).foldl (fun s i => setO (setO s (szOff w i) (2 ^ w - 1) 1)
        (parOff w (n * w) i) (2 ^ w - 1) i) 0) = 0 ∧
      ∀ i < j,
        Nat.land (Nat.shiftRight ((List.range j).foldl (fun s i => setO (setO s (szOff w i)
          (2 ^ w - 1) 1) (parOff w (n * w) i) (2 ^ w - 1) i) 0) (parOff w (n * w) i))
          (2 ^ w - 1) = i ∧
        Nat.land (Nat.shiftRight ((List.range j).foldl (fun s i => setO (setO s (szOff w i)
          (2 ^ w - 1) 1) (parOff w (n * w) i) (2 ^ w - 1) i) 0) (szOff w i)) (2 ^ w - 1) = 1
  | 0, _ => ⟨Nat.two_pow_pos _, rfl, by rw [List.range_zero, List.foldl_nil, kOf_eq, fld_zero],
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | j + 1, hj => by
    obtain ⟨hT, h0, hk, hf⟩ := init_inv hn j (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range j).foldl (fun s i => setO (setO s (szOff w i) (2 ^ w - 1) 1)
      (parOff w (n * w) i) (2 ^ w - 1) i) 0 = s at hT h0 hk hf
    have hjn : j < n := by omega
    have hwj := mul_lt_le (w := w) hjn
    have hnw : n * w = w * n := Nat.mul_comm n w
    have h1 : (1 : Nat) < 2 ^ w := by omega
    have hjw : j < 2 ^ w := by omega
    refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
    · exact setO_lt (setO_lt hT h1 (by rw [szOff_eq]; omega)) hjw (by rw [parOff_eq]; omega)
    · rw [mod2_eq, setO_other hjw (by rw [parOff_eq]; omega),
        setO_other h1 (by rw [szOff_eq]; omega), ← mod2_eq]
      exact h0
    · rw [kOf_eq, setO_other hjw (by rw [parOff_eq]; omega),
        setO_other h1 (by rw [szOff_eq]; omega), ← kOf_eq]
      exact hk
    · by_cases hij : i = j
      · subst hij
        refine ⟨setO_get hjw, ?_⟩
        rw [setO_other hjw (by rw [szOff_eq, parOff_eq]; omega), setO_get h1]
      · have hi' : i < j := by omega
        have hwi := mul_lt_le (w := w) (lt_trans hi' hjn)
        obtain ⟨e1, e2⟩ := hf i hi'
        refine ⟨?_, ?_⟩
        · rw [setO_other hjw (par_disj hij), setO_other h1 (by rw [szOff_eq, parOff_eq]; omega),
            e1]
        · rw [setO_other hjw (by rw [szOff_eq, parOff_eq]; omega), setO_other h1 (sz_disj hij),
            e2]

theorem rel_init {n w : Nat} {G : Array (Array Nat)} {b x Lp : Nat} (hn : n < 2 ^ w)
    (h2 : 2 < 2 ^ w) (hb : b < n) (hx : x < n) :
    Rel n w (n * w) G b x Lp
      ((Array.ofFn (n := n) fun i => i.val).set! x b, (Array.replicate n 1).set! b 2, #[(b, x)],
        #[])
      (initK n w (2 ^ w - 1) (n * w) b x) := by
  obtain ⟨hT, h0, hk, hf⟩ := init_inv (w := w) hn n le_rfl
  unfold initK
  simp only [strictN_eq]
  rw [foldUp_eq]
  generalize (List.range n).foldl (fun s i => setO (setO s (szOff w i) (2 ^ w - 1) 1)
      (parOff w (n * w) i) (2 ^ w - 1) i) 0 = s at hT h0 hk hf
  have hnw : n * w = w * n := Nat.mul_comm n w
  have hbw : b < 2 ^ w := by omega
  have hwb := mul_lt_le (w := w) hb
  have hwx := mul_lt_le (w := w) hx
  refine ⟨?_, ?_, by simp, by simp, fun j => ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [mod2_eq, setO_other h2 (by rw [szOff_eq]; omega),
      setO_other hbw (by rw [parOff_eq]; omega), ← mod2_eq]
    exact h0
  · exact setO_lt (setO_lt hT hbw (by rw [parOff_eq]; omega)) h2 (by rw [szOff_eq]; omega)
  · rw [setO_other h2 (by rw [szOff_eq, parOff_eq]; omega), set_get (by simpa using hx)]
    by_cases hjx : j = x
    · subst hjx
      rw [ite_eq_left rfl, setO_get hbw]
    · rw [ite_eq_right hjx]
      by_cases hjn : j < n
      · have hwj := mul_lt_le (w := w) hjn
        rw [setO_other hbw (par_disj hjx), (hf j hjn).1, getElem!_pos _ j (by simpa using hjn),
          Array.getElem_ofFn]
      · have hwj : w * n ≤ w * j := Nat.mul_le_mul_left w (by omega)
        rw [getElem!_neg _ j (by simpa using hjn),
          setO_other hbw (by rw [parOff_eq, parOff_eq]; omega),
          fld_high hT (by rw [parOff_eq]; omega)]
        rfl
  · rw [set_get (by simpa using hb)]
    have hwj := mul_lt_le (w := w) hj
    by_cases hjb : j = b
    · subst hjb
      rw [ite_eq_left rfl, setO_get h2]
    · rw [ite_eq_right hjb, setO_other h2 (sz_disj hjb),
        setO_other hbw (by rw [szOff_eq, parOff_eq]; omega), (hf j hj).2,
        getElem!_pos _ j (by simpa using hj), Array.getElem_replicate]
  · rw [kOf_eq, setO_other h2 (by rw [szOff_eq]; omega), setO_other hbw (by rw [parOff_eq]; omega),
      ← kOf_eq, hk]
    rfl
  · rfl

theorem mergeSearch_eq_of_searchK {n w m nw nG : Nat} {Gp : Nat → Nat} {b x cnt Lp : Nat}
    {G : Array (Array Nat)} (hGs : G.size = nG)
    (hGp : ∀ i < nG, ∀ y < n, (G[i]!)[y]! = pg w m (Gp i) y)
    (h : searchK n w m nw nG Gp b x cnt Lp = true) :
    mergeSearch n G b x =
      (List.range cnt).map fun j => (pg w m Lp (3 * j), pg w m Lp (3 * j + 1),
        pg w m Lp (3 * j + 2)) := by
  unfold searchK at h
  simp only [band_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, strictB_eq] at h
  obtain ⟨hm, hnw, hnm, h2m, hb, hx, hcnt, hf1, hf2⟩ := h
  rw [mask_eq] at hm
  subst hm hnw
  have hw0 := Nat.two_pow_pos w
  have hn : n < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hcnt' : cnt < 2 ^ 32 := hcnt
  rw [foldUp_eq] at hf1 hf2
  have hgood : ((List.range (n + 1)).foldl
      (fun t h => stepK n w (2 ^ w - 1) (n * w) nG cnt Lp Gp b x h t)
      (initK n w (2 ^ w - 1) (n * w) b x)) % 2 = 0 := by
    rw [← land_one]
    exact hf1
  have hrel := stepK_fold rfl hn hcnt' hGs hGp _ _ _ (rel_init (G := G) (Lp := Lp) hn h2 hb hx)
    hgood
  have hk : kOf ((List.range (n + 1)).foldl
      (fun t h => stepK n w (2 ^ w - 1) (n * w) nG cnt Lp Gp b x h t)
      (initK n w (2 ^ w - 1) (n * w) b x)) = cnt := hf2
  unfold mergeSearch
  rw [hrel.2.2.2.2.2.2.1, hk]
  rfl

end CFSG.KC.MergeR

end
