module

public import Certificates.Data.D4HexLocCheck
public import CFSG.Certificates.Kernel.S63K.OrbRunSound

public section

namespace CFSG.KC.S63K

open CFSG.D4Hex CFSG.LargeExtraspecial.S63 CFSG.KC.Enum CFSG.Monster.B.Co2.Native

@[expose] def locY (eT : EnumData) (j x : ℕ) : Array ℕ :=
  conjI locSteps[j]!.1 locSteps[j]!.2 eT.El[x]!

abbrev LfSt := Array Bool × Array ℕ × Array (ℕ × ℕ × ℕ)

abbrev LfO := Array Bool × Array ℕ × Array (ℕ × ℕ × ℕ) × ℕ

@[expose] def lInner (eT : EnumData) (p : ℕ) (j : ℕ) (r : LfSt) : Id (ForInStep LfSt) :=
  if (decide (eT.idx (locY eT j p) < eT.El.size) && eT.El[eT.idx (locY eT j p)]! == locY eT j p &&
      !r.1[eT.idx (locY eT j p)]!) = true then
    pure (ForInStep.yield (r.1.set! (eT.idx (locY eT j p)) true, r.2.1.push (eT.idx (locY eT j p)),
      r.2.2.push (eT.idx (locY eT j p), p, j)))
  else pure (ForInStep.yield (r.1, r.2.1, r.2.2))

@[expose] def lOuter (eT : EnumData) (_ : Unit) (r : LfO) : Id (ForInStep LfO) :=
  if r.2.2.2 < r.2.1.size then
    pure (ForInStep.yield ((fun t : LfSt => (t.1, t.2.1, t.2.2, r.2.2.2 + 1))
      (Id.run (forIn [:locSteps.size] (r.1, r.2.1, r.2.2.1) (lInner eT r.2.1[r.2.2.2]!)))))
  else pure (ForInStep.done r)

@[expose] def runL (eT : EnumData) (r : LfO) : LfO := Id.run (forIn Lean.Loop.mk r (lOuter eT))

@[expose] def lJ (eT : EnumData) (p : ℕ) (r : LfSt) (j : ℕ) : LfSt :=
  if (decide (eT.idx (locY eT j p) < eT.El.size) && eT.El[eT.idx (locY eT j p)]! == locY eT j p &&
      !r.1[eT.idx (locY eT j p)]!) = true then
    (r.1.set! (eT.idx (locY eT j p)) true, r.2.1.push (eT.idx (locY eT j p)),
      r.2.2.push (eT.idx (locY eT j p), p, j))
  else r

theorem locForest_eq_run (eT : EnumData) {r0 r1 : ℕ} (h0 : r0 < eT.El.size)
    (h1 : r1 < eT.El.size) :
    locForest eT [r0, r1] = (runL eT (((Array.replicate eT.El.size false).set! r0 true).set! r1
      true, #[r0, r1], #[], 0)).2.2.1.toList := by
  unfold locForest
  simp only [List.forIn_cons, List.forIn_nil, h0, h1, ↓reduceIte]
  rfl

theorem lInner_eq (eT : EnumData) (p : ℕ) (s : LfSt) :
    Id.run (forIn [:locSteps.size] s (lInner eT p)) =
      (List.range' 0 locSteps.size).foldl (lJ eT p) s := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply forIn_yield
  intro k t
  unfold lInner lJ
  split <;> rfl

theorem runL_unfold (eT : EnumData) (s : LfSt) (h : ℕ) :
    runL eT (s.1, s.2.1, s.2.2, h) = if h < s.2.1.size then
      runL eT ((fun t : LfSt => (t.1, t.2.1, t.2.2, h + 1))
        ((List.range' 0 locSteps.size).foldl (lJ eT s.2.1[h]!) s))
      else (s.1, s.2.1, s.2.2, h) := by
  unfold runL
  simp only [Id.run]
  rw [loop_unfold]
  unfold lOuter
  dsimp only
  by_cases hc : h < s.2.1.size
  · rw [if_pos hc, if_pos hc]
    dsimp only [pure]
    rw [lInner_eq]
  · rw [if_neg hc, if_neg hc]
    rfl

variable {eT : EnumData} {O Pa La W : ℕ → ℕ} {cnt : ℕ}

structure LfInv (eT : EnumData) (O Pa La : ℕ → ℕ) (cnt c : ℕ) (s : LfSt) : Prop where
  ssz : s.1.size = eT.El.size
  seen : ∀ w < cnt, s.1[O w]! = decide (w < c)
  qsz : s.2.1.size = c
  q : ∀ i < c, s.2.1[i]! = O i
  out : s.2.2.toList = (List.range' 2 (c - 2)).map fun i => (O i, O (Pa i), La i)

@[expose] def LTree (eT : EnumData) (O Pa La : ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i < c → Pa i < i ∧ La i < locSteps.size ∧
    memR eT.El eT.idx (locY eT (La i) (O (Pa i))) = true ∧
    eT.idx (locY eT (La i) (O (Pa i))) = O i

@[expose] def LAct (eT : EnumData) (O W : ℕ → ℕ) (cnt : ℕ) : Prop :=
  ∀ h < cnt, ∀ j < locSteps.size,
    (memR eT.El eT.idx (locY eT j (O h)) = true ∧
      eT.idx (locY eT j (O h)) = O (W (locSteps.size * h + j))) ∨
    (memR eT.El eT.idx (locY eT j (O h)) = false ∧ W (locSteps.size * h + j) = 0)

theorem getB_set (a : Array Bool) {i j : ℕ} (v : Bool) (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  rw [getElem!_pos _ j (by simp [hj]), getElem!_pos a j hj]
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds hj]

theorem memR_def (El : Array (Array ℕ)) (idx : Array ℕ → ℕ) (y : Array ℕ) :
    (decide (idx y < El.size) && El[idx y]! == y) = memR El idx y := rfl

theorem linv_push {c : ℕ} {s : LfSt} (hO : ∀ i < cnt, O i < eT.El.size)
    (hinj : ∀ a < cnt, ∀ b < cnt, O a = O b → a = b) (hs : LfInv eT O Pa La cnt c s)
    (hc : c < cnt) (h2 : 2 ≤ c) {p j : ℕ} (hPa : O (Pa c) = p) (hLa : La c = j) :
    LfInv eT O Pa La cnt (c + 1) (s.1.set! (O c) true, s.2.1.push (O c), s.2.2.push (O c, p, j)) := by
  obtain ⟨hssz, hseen, hqsz, hq, hout⟩ := hs
  refine ⟨by simp [hssz], fun w hw => ?_, by simp [hqsz], fun i hi => ?_, ?_⟩
  · dsimp only
    have hlt : O w < s.1.size := by rw [hssz]; exact hO w hw
    rw [getB_set _ _ hlt]
    by_cases e : O c = O w
    · have := hinj c hc w hw e
      subst this
      simp
    · rw [if_neg e, hseen w hw]
      have : w ≠ c := fun h => e (by rw [h])
      simp only [decide_eq_decide]
      omega
  · dsimp only
    rw [push_get _ _ hqsz hi]
    split
    · exact hq i ‹_›
    · congr 1
      omega
  · dsimp only
    rw [Array.toList_push, hout]
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 2 := ⟨c - 2, by omega⟩
    rw [Nat.add_sub_cancel, show m + 2 + 1 - 2 = m + 1 by omega, List.range'_concat,
      List.map_append, List.map_cons, List.map_nil, show 2 + 1 * m = m + 2 by omega, hPa, hLa]

theorem lrow_replay (hO : ∀ i < cnt, O i < eT.El.size)
    (hinj : ∀ a < cnt, ∀ b < cnt, O a = O b → a = b) (hact : LAct eT O W cnt) {h : ℕ} :
    ∀ n j c (s : LfSt), j + n ≤ locSteps.size → h < c → 2 ≤ c →
      LfInv eT O Pa La cnt c s → LTree eT O Pa La c →
      orbRowK W Pa La locSteps.size h n j c ≠ 0 → orbRowK W Pa La locSteps.size h n j c ≤ cnt →
      LfInv eT O Pa La cnt (orbRowK W Pa La locSteps.size h n j c)
          ((List.range' j n).foldl (lJ eT (O h)) s) ∧
        LTree eT O Pa La (orbRowK W Pa La locSteps.size h n j c) := by
  intro n
  induction n with
  | zero =>
    intro j c s _ _ _ hs ht _ _
    exact ⟨hs, ht⟩
  | succ n ih =>
    intro j c s hjn hhc h2 hs ht hne hle
    have hmono := orbRowK_mono (W := W) (Pa := Pa) (La := La) (k := locSteps.size) h (n + 1) j c
      hne
    have hcc : c ≤ cnt := Nat.le_trans hmono hle
    rw [List.range'_succ, List.foldl_cons]
    rw [orbRowK_succ] at hne hle hmono ⊢
    unfold lJ
    rw [memR_def]
    rcases hact h (by omega) j (by omega) with ⟨hm, hi⟩ | ⟨hm, hw0⟩
    · rw [hm, hi, Bool.true_and]
      by_cases hw : W (locSteps.size * h + j) < c
      · rw [if_pos hw] at hne hle hmono ⊢
        rw [hs.seen _ (by omega), decide_eq_true hw]
        exact ih (j + 1) c s (by omega) hhc h2 hs ht hne hle
      · rw [if_neg hw] at hne hle hmono ⊢
        by_cases hn : W (locSteps.size * h + j) = c ∧ Pa c = h ∧ La c = j
        · rw [if_pos hn] at hne hle hmono ⊢
          obtain ⟨hwc, hpc, hlc⟩ := hn
          have hcN : c < cnt := Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
            (Nat.le_trans (orbRowK_mono h n (j + 1) (c + 1) hne) hle)
          rw [hwc, hs.seen c hcN, decide_eq_false (Nat.lt_irrefl c)]
          simp only [Bool.not_false, ↓reduceIte]
          have hpush := linv_push (Pa := Pa) (La := La) (p := O h) (j := j) hO hinj hs hcN h2
            (by rw [hpc]) hlc
          refine ih (j + 1) (c + 1) _ (by omega) (by omega) (by omega) hpush
            (fun i h0 hi' => ?_) hne hle
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · exact ht i h0 hi'
          · refine ⟨by omega, by omega, ?_, ?_⟩
            · rw [hpc, hlc]
              exact hm
            · rw [hpc, hlc, hi, hwc]
        · rw [if_neg hn] at hne
          exact absurd rfl hne
    · rw [hm, Bool.false_and]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hw0, if_pos (by omega)] at hne hle ⊢
      exact ih (j + 1) c s (by omega) hhc h2 hs ht hne hle

theorem lrun_replay (hO : ∀ i < cnt, O i < eT.El.size)
    (hinj : ∀ a < cnt, ∀ b < cnt, O a = O b → a = b) (hact : LAct eT O W cnt) :
    ∀ fuel h c (s : LfSt), c ≤ cnt → 2 ≤ c →
      LfInv eT O Pa La cnt c s → LTree eT O Pa La c →
      orbRunK W Pa La locSteps.size fuel h c = cnt →
      LfInv eT O Pa La cnt cnt ((fun r : LfO => (r.1, r.2.1, r.2.2.1))
        (runL eT (s.1, s.2.1, s.2.2, h))) ∧ LTree eT O Pa La cnt := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s _ _ _ _ hr
    have : orbRunK W Pa La locSteps.size 0 h c = 0 := rfl
    omega
  | succ fuel ih =>
    intro h c s hcN h2 hs ht hr
    have hmono := orbRunK_mono (W := W) (Pa := Pa) (La := La) (k := locSteps.size) (fuel + 1) h c
      (by omega)
    rw [orbRunK_succ] at hr hmono
    rw [runL_unfold, hs.qsz]
    by_cases hc : h < c
    · rw [if_pos hc] at hr hmono ⊢
      by_cases h0 : orbRowK W Pa La locSteps.size h locSteps.size 0 c = 0
      · rw [if_pos h0] at hr
        omega
      · rw [if_neg h0] at hr hmono
        have hle : orbRowK W Pa La locSteps.size h locSteps.size 0 c ≤ cnt :=
          hr ▸ orbRunK_mono fuel (h + 1) _ (by omega)
        rw [hs.q h hc]
        obtain ⟨hs', ht'⟩ := lrow_replay hO hinj hact locSteps.size 0 c s (by omega) hc h2 hs ht
          h0 hle
        exact ih (h + 1) _ _ hle (Nat.le_trans h2 (orbRowK_mono h _ _ _ h0)) hs' ht' hr
    · rw [if_neg hc] at hr ⊢
      subst hr
      exact ⟨hs, ht⟩

theorem locForest_of_K (hcnt : 2 ≤ cnt) (hO : ∀ i < cnt, O i < eT.El.size)
    (hinj : ∀ a < cnt, ∀ b < cnt, O a = O b → a = b) (hact : LAct eT O W cnt)
    (hrun : orbRunK W Pa La locSteps.size (cnt + 1) 0 2 = cnt) :
    locForest eT [O 0, O 1] = ((List.range' 2 (cnt - 2)).map fun i => (O i, O (Pa i), La i)) ∧
      LTree eT O Pa La cnt := by
  have h0 := hO 0 (by omega)
  have h1 := hO 1 (by omega)
  have hs0 : LfInv eT O Pa La cnt 2 (((Array.replicate eT.El.size false).set! (O 0) true).set!
      (O 1) true, #[O 0, O 1], #[]) := by
    refine ⟨by simp, fun w hw => ?_, rfl, fun i hi => ?_, rfl⟩
    · dsimp only
      have hw' := hO w hw
      rw [getB_set _ _ (by simpa using hw'), getB_set _ _ (by simpa using hw'),
        getElem!_pos _ _ (by simpa using hw'), Array.getElem_replicate]
      by_cases e1 : O 1 = O w
      · have := hinj 1 (by omega) w hw e1
        subst this
        simp
      · by_cases e0 : O 0 = O w
        · have := hinj 0 (by omega) w hw e0
          subst this
          simp
        · rw [if_neg e1, if_neg e0]
          have : w ≠ 0 := fun h => e0 (by rw [h])
          have : w ≠ 1 := fun h => e1 (by rw [h])
          simp only [Bool.false_eq, decide_eq_false_iff_not]
          omega
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · rfl
      · rfl
  obtain ⟨hs, ht⟩ := lrun_replay (Pa := Pa) (La := La) hO hinj hact (cnt + 1) 0 2 _ hcnt
    (le_refl 2) hs0 (fun i h2 hi => by omega) hrun
  refine ⟨?_, ht⟩
  rw [locForest_eq_run eT h0 h1, ← hs.out]

abbrev PSt := Std.HashSet (ℕ × ℕ) × Array (ℕ × ℕ) × Array ((ℕ × ℕ) × (ℕ × ℕ) × ℕ)

abbrev PO := Std.HashSet (ℕ × ℕ) × Array (ℕ × ℕ) × Array ((ℕ × ℕ) × (ℕ × ℕ) × ℕ) × ℕ

@[expose] def pCond (eT : EnumData) (p : ℕ × ℕ) (j : ℕ) (r : PSt) : Bool :=
  decide (eT.idx (locY eT j p.1) < eT.El.size) && decide (eT.idx (locY eT j p.2) < eT.El.size) &&
    eT.El[eT.idx (locY eT j p.1)]! == locY eT j p.1 &&
    eT.El[eT.idx (locY eT j p.2)]! == locY eT j p.2 &&
    !r.1.contains (eT.idx (locY eT j p.1), eT.idx (locY eT j p.2))

@[expose] def pInner (eT : EnumData) (p : ℕ × ℕ) (j : ℕ) (r : PSt) : Id (ForInStep PSt) :=
  if pCond eT p j r = true then
    pure (ForInStep.yield (r.1.insert (eT.idx (locY eT j p.1), eT.idx (locY eT j p.2)),
      r.2.1.push (eT.idx (locY eT j p.1), eT.idx (locY eT j p.2)),
      r.2.2.push ((eT.idx (locY eT j p.1), eT.idx (locY eT j p.2)), p, j)))
  else pure (ForInStep.yield (r.1, r.2.1, r.2.2))

@[expose] def pOuter (eT : EnumData) (_ : Unit) (r : PO) : Id (ForInStep PO) :=
  if r.2.2.2 < r.2.1.size then
    pure (ForInStep.yield ((fun t : PSt => (t.1, t.2.1, t.2.2, r.2.2.2 + 1))
      (Id.run (forIn [:locSteps.size] (r.1, r.2.1, r.2.2.1) (pInner eT r.2.1[r.2.2.2]!)))))
  else pure (ForInStep.done r)

@[expose] def runP (eT : EnumData) (r : PO) : PO := Id.run (forIn Lean.Loop.mk r (pOuter eT))

@[expose] def pJ (eT : EnumData) (p : ℕ × ℕ) (r : PSt) (j : ℕ) : PSt :=
  if pCond eT p j r = true then
    (r.1.insert (eT.idx (locY eT j p.1), eT.idx (locY eT j p.2)),
      r.2.1.push (eT.idx (locY eT j p.1), eT.idx (locY eT j p.2)),
      r.2.2.push ((eT.idx (locY eT j p.1), eT.idx (locY eT j p.2)), p, j))
  else r

theorem locPairForest_eq_run (eT : EnumData) (start : ℕ × ℕ) :
    locPairForest eT start =
      (runP eT ((∅ : Std.HashSet (ℕ × ℕ)).insert start, #[start], #[], 0)).2.2.1.toList := by
  unfold locPairForest
  rfl

theorem pInner_eq (eT : EnumData) (p : ℕ × ℕ) (s : PSt) :
    Id.run (forIn [:locSteps.size] s (pInner eT p)) =
      (List.range' 0 locSteps.size).foldl (pJ eT p) s := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply forIn_yield
  intro k t
  unfold pInner pJ
  split <;> rfl

theorem runP_unfold (eT : EnumData) (s : PSt) (h : ℕ) :
    runP eT (s.1, s.2.1, s.2.2, h) = if h < s.2.1.size then
      runP eT ((fun t : PSt => (t.1, t.2.1, t.2.2, h + 1))
        ((List.range' 0 locSteps.size).foldl (pJ eT s.2.1[h]!) s))
      else (s.1, s.2.1, s.2.2, h) := by
  unfold runP
  simp only [Id.run]
  rw [loop_unfold]
  unfold pOuter
  dsimp only
  by_cases hc : h < s.2.1.size
  · rw [if_pos hc, if_pos hc]
    dsimp only [pure]
    rw [pInner_eq]
  · rw [if_neg hc, if_neg hc]
    rfl

variable {A B : ℕ → ℕ}

structure PInv (A B Pa La : ℕ → ℕ) (cnt c : ℕ) (s : PSt) : Prop where
  seen : ∀ w < cnt, s.1.contains (A w, B w) = decide (w < c)
  qsz : s.2.1.size = c
  q : ∀ i < c, s.2.1[i]! = (A i, B i)
  out : s.2.2.toList = (List.range' 1 (c - 1)).map fun i => ((A i, B i), (A (Pa i), B (Pa i)), La i)

@[expose] def PTree (eT : EnumData) (A B Pa La : ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i < c → Pa i < i ∧ La i < locSteps.size ∧
    memR eT.El eT.idx (locY eT (La i) (A (Pa i))) = true ∧
    memR eT.El eT.idx (locY eT (La i) (B (Pa i))) = true ∧
    eT.idx (locY eT (La i) (A (Pa i))) = A i ∧ eT.idx (locY eT (La i) (B (Pa i))) = B i

@[expose] def PAct (eT : EnumData) (A B W : ℕ → ℕ) (cnt : ℕ) : Prop :=
  ∀ h < cnt, ∀ j < locSteps.size,
    (memR eT.El eT.idx (locY eT j (A h)) = true ∧ memR eT.El eT.idx (locY eT j (B h)) = true ∧
      eT.idx (locY eT j (A h)) = A (W (locSteps.size * h + j)) ∧
      eT.idx (locY eT j (B h)) = B (W (locSteps.size * h + j))) ∨
    ((memR eT.El eT.idx (locY eT j (A h)) && memR eT.El eT.idx (locY eT j (B h))) = false ∧
      W (locSteps.size * h + j) = 0)

theorem and5 (a b c d e : Bool) : (a && b && c && d && e) = ((a && c) && (b && d) && e) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

theorem pCond_eq (eT : EnumData) (p : ℕ × ℕ) (j : ℕ) (r : PSt) :
    pCond eT p j r = (memR eT.El eT.idx (locY eT j p.1) && memR eT.El eT.idx (locY eT j p.2) &&
      !r.1.contains (eT.idx (locY eT j p.1), eT.idx (locY eT j p.2))) := by
  unfold pCond
  rw [and5]
  rfl

theorem pinv_push {c : ℕ} {s : PSt} (hinj : ∀ a < cnt, ∀ b < cnt, A a = A b → B a = B b → a = b)
    (hs : PInv A B Pa La cnt c s) (hc : c < cnt) (h1 : 1 ≤ c) {p : ℕ × ℕ} {j : ℕ}
    (hPa : (A (Pa c), B (Pa c)) = p) (hLa : La c = j) :
    PInv A B Pa La cnt (c + 1)
      (s.1.insert (A c, B c), s.2.1.push (A c, B c), s.2.2.push ((A c, B c), p, j)) := by
  obtain ⟨hseen, hqsz, hq, hout⟩ := hs
  refine ⟨fun w hw => ?_, by simp [hqsz], fun i hi => ?_, ?_⟩
  · dsimp only
    rw [Std.HashSet.contains_insert, hseen w hw]
    by_cases e : (A c, B c) = (A w, B w)
    · obtain ⟨ea, eb⟩ := Prod.mk.inj e
      have := hinj c hc w hw ea eb
      subst this
      simp
    · rw [beq_eq_false_iff_ne.2 e, Bool.false_or]
      have : w ≠ c := fun h => e (by rw [h])
      simp only [decide_eq_decide]
      omega
  · dsimp only
    rw [push_get _ _ hqsz hi]
    split
    · exact hq i ‹_›
    · congr 1 <;> congr 1 <;> omega
  · dsimp only
    rw [Array.toList_push, hout]
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, List.range'_concat,
      List.map_append, List.map_cons, List.map_nil, show 1 + 1 * m = m + 1 by omega, hPa, hLa]

theorem prow_replay (hinj : ∀ a < cnt, ∀ b < cnt, A a = A b → B a = B b → a = b)
    (hact : PAct eT A B W cnt) {h : ℕ} :
    ∀ n j c (s : PSt), j + n ≤ locSteps.size → h < c → 1 ≤ c →
      PInv A B Pa La cnt c s → PTree eT A B Pa La c →
      orbRowK W Pa La locSteps.size h n j c ≠ 0 → orbRowK W Pa La locSteps.size h n j c ≤ cnt →
      PInv A B Pa La cnt (orbRowK W Pa La locSteps.size h n j c)
          ((List.range' j n).foldl (pJ eT (A h, B h)) s) ∧
        PTree eT A B Pa La (orbRowK W Pa La locSteps.size h n j c) := by
  intro n
  induction n with
  | zero =>
    intro j c s _ _ _ hs ht _ _
    exact ⟨hs, ht⟩
  | succ n ih =>
    intro j c s hjn hhc h1 hs ht hne hle
    have hmono := orbRowK_mono (W := W) (Pa := Pa) (La := La) (k := locSteps.size) h (n + 1) j c
      hne
    have hcc : c ≤ cnt := Nat.le_trans hmono hle
    rw [List.range'_succ, List.foldl_cons]
    rw [orbRowK_succ] at hne hle hmono ⊢
    unfold pJ
    rw [pCond_eq]
    dsimp only
    rcases hact h (by omega) j (by omega) with ⟨hma, hmb, hia, hib⟩ | ⟨hm, hw0⟩
    · rw [hma, hmb, hia, hib, Bool.true_and, Bool.true_and]
      by_cases hw : W (locSteps.size * h + j) < c
      · rw [if_pos hw] at hne hle hmono ⊢
        rw [hs.seen _ (by omega), decide_eq_true hw]
        exact ih (j + 1) c s (by omega) hhc h1 hs ht hne hle
      · rw [if_neg hw] at hne hle hmono ⊢
        by_cases hn : W (locSteps.size * h + j) = c ∧ Pa c = h ∧ La c = j
        · rw [if_pos hn] at hne hle hmono ⊢
          obtain ⟨hwc, hpc, hlc⟩ := hn
          have hcN : c < cnt := Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
            (Nat.le_trans (orbRowK_mono h n (j + 1) (c + 1) hne) hle)
          rw [hwc, hs.seen c hcN, decide_eq_false (Nat.lt_irrefl c)]
          simp only [Bool.not_false, ↓reduceIte]
          have hpush := pinv_push (Pa := Pa) (La := La) (p := (A h, B h)) (j := j) hinj hs hcN h1
            (by rw [hpc]) hlc
          refine ih (j + 1) (c + 1) _ (by omega) (by omega) (by omega) hpush
            (fun i h0 hi' => ?_) hne hle
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · exact ht i h0 hi'
          · refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
            · rw [hpc, hlc]
              exact hma
            · rw [hpc, hlc]
              exact hmb
            · rw [hpc, hlc, hia, hwc]
            · rw [hpc, hlc, hib, hwc]
        · rw [if_neg hn] at hne
          exact absurd rfl hne
    · rw [hm, Bool.false_and]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hw0, if_pos (by omega)] at hne hle ⊢
      exact ih (j + 1) c s (by omega) hhc h1 hs ht hne hle

theorem prun_replay (hinj : ∀ a < cnt, ∀ b < cnt, A a = A b → B a = B b → a = b)
    (hact : PAct eT A B W cnt) :
    ∀ fuel h c (s : PSt), c ≤ cnt → 1 ≤ c →
      PInv A B Pa La cnt c s → PTree eT A B Pa La c →
      orbRunK W Pa La locSteps.size fuel h c = cnt →
      PInv A B Pa La cnt cnt ((fun r : PO => (r.1, r.2.1, r.2.2.1))
        (runP eT (s.1, s.2.1, s.2.2, h))) ∧ PTree eT A B Pa La cnt := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s _ _ _ _ hr
    have : orbRunK W Pa La locSteps.size 0 h c = 0 := rfl
    omega
  | succ fuel ih =>
    intro h c s hcN h1 hs ht hr
    have hmono := orbRunK_mono (W := W) (Pa := Pa) (La := La) (k := locSteps.size) (fuel + 1) h c
      (by omega)
    rw [orbRunK_succ] at hr hmono
    rw [runP_unfold, hs.qsz]
    by_cases hc : h < c
    · rw [if_pos hc] at hr hmono ⊢
      by_cases h0 : orbRowK W Pa La locSteps.size h locSteps.size 0 c = 0
      · rw [if_pos h0] at hr
        omega
      · rw [if_neg h0] at hr hmono
        have hle : orbRowK W Pa La locSteps.size h locSteps.size 0 c ≤ cnt :=
          hr ▸ orbRunK_mono fuel (h + 1) _ (by omega)
        rw [hs.q h hc]
        obtain ⟨hs', ht'⟩ := prow_replay hinj hact locSteps.size 0 c s (by omega) hc h1 hs ht
          h0 hle
        exact ih (h + 1) _ _ hle (Nat.le_trans h1 (orbRowK_mono h _ _ _ h0)) hs' ht' hr
    · rw [if_neg hc] at hr ⊢
      subst hr
      exact ⟨hs, ht⟩

theorem locPairForest_of_K (hcnt : 1 ≤ cnt)
    (hinj : ∀ a < cnt, ∀ b < cnt, A a = A b → B a = B b → a = b) (hact : PAct eT A B W cnt)
    (hrun : orbRunK W Pa La locSteps.size (cnt + 1) 0 1 = cnt) :
    locPairForest eT (A 0, B 0) =
        ((List.range' 1 (cnt - 1)).map fun i => ((A i, B i), (A (Pa i), B (Pa i)), La i)) ∧
      PTree eT A B Pa La cnt := by
  have hs0 : PInv A B Pa La cnt 1
      ((∅ : Std.HashSet (ℕ × ℕ)).insert (A 0, B 0), #[(A 0, B 0)], #[]) := by
    refine ⟨fun w hw => ?_, rfl, fun i hi => ?_, rfl⟩
    · dsimp only
      rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
      by_cases e : (A 0, B 0) = (A w, B w)
      · obtain ⟨ea, eb⟩ := Prod.mk.inj e
        have := hinj 0 hcnt w hw ea eb
        subst this
        simp
      · rw [beq_eq_false_iff_ne.2 e]
        have : w ≠ 0 := fun h => e (by rw [h])
        simp only [Bool.false_eq, decide_eq_false_iff_not]
        omega
    · obtain rfl : i = 0 := by omega
      rfl
  obtain ⟨hs, ht⟩ := prun_replay (Pa := Pa) (La := La) hinj hact (cnt + 1) 0 1 _ hcnt
    (le_refl 1) hs0 (fun i h1 hi => by omega) hrun
  refine ⟨?_, ht⟩
  rw [locPairForest_eq_run, ← hs.out]

end CFSG.KC.S63K

end
