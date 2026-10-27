module

public import CFSG.Certificates.Kernel.Spor.PK.BFS
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.KS.PK

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

@[expose] def tabF (letters : Array Table) (l x : Nat) : Nat := ap letters[l]! x

@[expose] def treeOf (n : Nat) (s : BS) : Tree :=
  ⟨(s.pts.map UInt32.ofNat).toArray,
    Array.ofFn (n := n) fun x => if x.val ∈ s.pts then UInt32.ofNat (s.pts.idxOf x.val) else none32 (),
    (s.par.map UInt32.ofNat).toArray, (s.lab.map UInt32.ofNat).toArray⟩

private theorem foldl_fixed {β : Type} (g : β → Nat → β) (b : β) :
    ∀ l : List Nat, (∀ h ∈ l, g b h = b) → l.foldl g b = b
  | [], _ => rfl
  | h :: l, H => by
    rw [List.foldl_cons, H h (List.mem_cons_self ..)]
    exact foldl_fixed g b l fun h' hh' => H h' (List.mem_cons_of_mem _ hh')

private theorem forIn_range'_break {β : Type} (f : Nat → β → β) (c : Nat → β → Prop)
    [∀ h b, Decidable (c h b)] (hmono : ∀ h h' b, h ≤ h' → ¬ c h b → ¬ c h' b) :
    ∀ (k s : Nat) (b : β),
      forIn (m := Id) (List.range' s k) b
          (fun h b => if c h b then pure (ForInStep.yield (f h b)) else pure (ForInStep.done b)) =
        (List.range' s k).foldl (fun b h => if c h b then f h b else b) b
  | 0, _, _ => rfl
  | k + 1, s, b => by
    rw [List.range'_succ, List.forIn_cons, List.foldl_cons]
    by_cases hc : c s b
    · simp only [hc, if_true, pure_bind]
      exact forIn_range'_break f c hmono k (s + 1) (f s b)
    · simp only [hc, if_false, pure_bind]
      refine (foldl_fixed _ b _ fun h hh => ?_).symm
      rw [List.mem_range'_1] at hh
      exact if_neg (hmono s h b (by omega) hc)

private theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

private abbrev NS := Table × Table × Table × Table

private def initN (n root : Nat) : NS :=
  ((Array.replicate n none32).set! root 0, #[UInt32.ofNat root], #[0], #[0])

private def letterN (letters : Array Table) (h p : Nat) (b : NS) (l : Nat) : NS :=
  if (b.1[tabF letters l p]! == none32 ()) = true then
    (b.1.set! (tabF letters l p) (UInt32.ofNat b.2.1.size),
      b.2.1.push (UInt32.ofNat (tabF letters l p)), b.2.2.1.push (UInt32.ofNat h),
      b.2.2.2.push (UInt32.ofNat l))
  else b

private def stepN (letters : Array Table) (lv : Array Nat) (b : NS) (h : Nat) : NS :=
  if h < b.2.1.size then lv.toList.foldl (letterN letters h (ap b.2.1 h)) b else b

private def finalN (b : NS) : Tree := ⟨b.2.1, b.1, b.2.2.1, b.2.2.2⟩

private theorem treeBFS_eq_foldl (n root : Nat) (letters : Array Table) (lv : Array Nat) :
    treeBFS n root letters lv =
      finalN ((List.range n).foldl (stepN letters lv) (initN n root)) := by
  unfold treeBFS
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← Array.forIn_toList, ite_pure_yield, List.forIn_pure_yield_eq_foldl, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, pure_bind, bind_pure, Prod.eta]
  rw [List.range_eq_range']
  exact congrArg finalN (forIn_range'_break (β := NS)
    (fun h b => lv.toList.foldl (letterN letters h (ap b.2.1 h)) b) (fun h b => h < b.2.1.size)
    (fun h h' b hh hc hc' => hc (by omega)) n 0 (initN n root))

private theorem toNat_ofNat_lt {k : Nat} (hk : k < 2 ^ 32) : (UInt32.ofNat k).toNat = k := by
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hk

private theorem ofNat_ne_none32 {k : Nat} (hk : k + 1 < 2 ^ 32) : UInt32.ofNat k ≠ none32 () := by
  intro h
  have h1 := congrArg UInt32.toNat h
  rw [toNat_ofNat_lt (by omega)] at h1
  have h2 : (none32 ()).toNat = 4294967295 := rfl
  rw [h2] at h1
  omega

private theorem getD_mem' {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem getElem!_mapOfNat (l : List Nat) {h : Nat} (hh : h < l.length) :
    ((l.map UInt32.ofNat).toArray)[h]! = UInt32.ofNat (l.getD h 0) := by
  rw [getElem!_pos _ h (by simpa using hh)]
  simp [List.getD_eq_getElem?_getD, hh]

private theorem ap_mapOfNat {n : Nat} (hn : n < 2 ^ 32) {l : List Nat} (hl : ∀ p ∈ l, p < n)
    {h : Nat} (hh : h < l.length) : ap ((l.map UInt32.ofNat).toArray) h = l.getD h 0 := by
  unfold ap
  rw [getElem!_mapOfNat l hh, toNat_ofNat_lt (Nat.lt_trans (hl _ (getD_mem' hh)) hn)]

private theorem length_le_of_nodup' {n : Nat} {l : List Nat} (hl : l.Nodup) (h : ∀ p ∈ l, p < n) :
    l.length ≤ n := by
  have := hl.length_le_of_subset (l₂ := List.range n) fun p hp => List.mem_range.2 (h p hp)
  simpa using this

private structure Rel (n : Nat) (s : BS) (b : NS) : Prop where
  size : b.1.size = n
  pts : b.2.1 = (s.pts.map UInt32.ofNat).toArray
  par : b.2.2.1 = (s.par.map UInt32.ofNat).toArray
  lab : b.2.2.2 = (s.lab.map UInt32.ofNat).toArray
  pos : ∀ x < n, b.1[x]! = if x ∈ s.pts then UInt32.ofNat (s.pts.idxOf x) else none32 ()
  nodup : s.pts.Nodup
  lt : ∀ p ∈ s.pts, p < n

private theorem letter_rel {n : Nat} (hn : n < 2 ^ 32) {letters : Array Table} {lv : List Nat}
    (hF : ∀ l ∈ lv, ∀ x < n, tabF letters l x < n) {s : BS} {b : NS} (hs : Rel n s b)
    {h p : Nat} (hp : p < n) {l : Nat} (hl : l ∈ lv) :
    Rel n (BS.letter (tabF letters) h p s l) (letterN letters h p b l) := by
  have hq : tabF letters l p < n := hF l hl p hp
  have hlen : s.pts.length ≤ n := length_le_of_nodup' hs.nodup hs.lt
  have hv := hs.pos _ hq
  unfold BS.letter letterN
  by_cases hmem : tabF letters l p ∈ s.pts
  · have hne : b.1[tabF letters l p]! ≠ none32 () := by
      rw [hv, if_pos hmem]
      exact ofNat_ne_none32 (by have := List.idxOf_lt_length_of_mem hmem; omega)
    rw [if_pos hmem, if_neg (by simpa using hne)]
    exact hs
  · rw [if_neg hmem, hv, if_neg hmem, if_pos (by simp)]
    have hsz : b.2.1.size = s.pts.length := by rw [hs.pts]; simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Array.size_set!]
      exact hs.size
    · show b.2.1.push (UInt32.ofNat (tabF letters l p)) = _
      rw [hs.pts, List.push_toArray, List.map_append]
      rfl
    · show b.2.2.1.push (UInt32.ofNat h) = _
      rw [hs.par, List.push_toArray, List.map_append]
      rfl
    · show b.2.2.2.push (UInt32.ofNat l) = _
      rw [hs.lab, List.push_toArray, List.map_append]
      rfl
    · intro x hx
      by_cases e : x = tabF letters l p
      · subst e
        rw [Array.getElem!_set!_self _ _ _ (by rw [hs.size]; exact hq), hsz, if_pos (by simp),
          List.idxOf_append, if_neg hmem]
        simp
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e), hs.pos x hx]
        by_cases hx' : x ∈ s.pts
        · rw [if_pos hx', if_pos (List.mem_append_left _ hx'), List.idxOf_append, if_pos hx']
        · rw [if_neg hx', if_neg]
          simp [hx', e]
    · rw [List.nodup_append]
      refine ⟨hs.nodup, by simp, ?_⟩
      intro a ha b' hb
      rw [List.mem_singleton] at hb
      rintro rfl
      exact hmem (hb ▸ ha)
    · intro q hq'
      rcases List.mem_append.1 hq' with hq' | hq'
      · exact hs.lt q hq'
      · rw [List.mem_singleton] at hq'
        exact hq' ▸ hq

private theorem foldl_letter_rel {n : Nat} (hn : n < 2 ^ 32) {letters : Array Table} {lv : List Nat}
    (hF : ∀ l ∈ lv, ∀ x < n, tabF letters l x < n) {h p : Nat} (hp : p < n) :
    ∀ (lv' : List Nat), (∀ l ∈ lv', l ∈ lv) → ∀ {s : BS} {b : NS}, Rel n s b →
      Rel n (lv'.foldl (BS.letter (tabF letters) h p) s) (lv'.foldl (letterN letters h p) b)
  | [], _, _, _, hs => hs
  | l :: lv', hsub, s, b, hs => by
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_letter_rel hn hF hp lv' (fun l' hl' => hsub l' (List.mem_cons_of_mem _ hl'))
      (letter_rel hn hF hs hp (hsub l (List.mem_cons_self ..)))

private theorem step_rel {n : Nat} (hn : n < 2 ^ 32) {letters : Array Table} {lv : Array Nat}
    (hF : ∀ l ∈ lv.toList, ∀ x < n, tabF letters l x < n) {s : BS} {b : NS} (hs : Rel n s b)
    (h : Nat) : Rel n (BS.step (tabF letters) lv.toList s h) (stepN letters lv b h) := by
  unfold BS.step stepN
  have hsz : b.2.1.size = s.pts.length := by rw [hs.pts]; simp
  by_cases hh : h < s.pts.length
  · rw [if_pos hh, if_pos (hsz ▸ hh)]
    have hap : ap b.2.1 h = s.pts.getD h 0 := by
      rw [hs.pts]
      exact ap_mapOfNat hn hs.lt hh
    rw [hap]
    exact foldl_letter_rel hn hF (hs.lt _ (getD_mem' hh)) lv.toList (fun l hl => hl) hs
  · rw [if_neg hh, if_neg (by omega)]
    exact hs

private theorem init_rel {n root : Nat} (hr : root < n) : Rel n ⟨[root], [0], [0]⟩ (initN n root) := by
  refine ⟨?_, rfl, rfl, rfl, ?_, by simp, ?_⟩
  · simp [initN]
  · intro x hx
    simp only [initN]
    by_cases e : x = root
    · subst e
      rw [Array.getElem!_set!_self _ _ _ (by simp [hr])]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e), getElem!_pos _ _ (by simpa using hx),
        Array.getElem_replicate]
      simp [e]
  · intro p hp
    simp only [List.mem_singleton] at hp
    omega

private theorem run_rel {n root : Nat} (hn : n < 2 ^ 32) (hr : root < n) {letters : Array Table}
    {lv : Array Nat} (hF : ∀ l ∈ lv.toList, ∀ x < n, tabF letters l x < n) (k : Nat) :
    Rel n ((List.range k).foldl (BS.step (tabF letters) lv.toList) ⟨[root], [0], [0]⟩)
      ((List.range k).foldl (stepN letters lv) (initN n root)) := by
  induction k with
  | zero => exact init_rel hr
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil]
    exact step_rel hn hF ih k

private theorem finalN_eq {n : Nat} {s : BS} {b : NS} (hs : Rel n s b) : finalN b = treeOf n s := by
  unfold finalN treeOf
  rw [hs.pts, hs.par, hs.lab]
  congr 1
  apply Array.ext (by rw [hs.size]; simp)
  intro i h1 h2
  rw [Array.getElem_ofFn, ← getElem!_pos b.1 i h1, hs.pos i (by simpa using h2)]

theorem treeBFS_eq {n root : Nat} {letters : Array Table} {lv : Array Nat} (hn : n < 2 ^ 32)
    (hr : root < n) (hF : ∀ l ∈ lv.toList, ∀ x < n, tabF letters l x < n) :
    treeBFS n root letters lv = treeOf n (BS.run (tabF letters) lv.toList n root) := by
  rw [treeBFS_eq_foldl]
  exact finalN_eq (run_rel hn hr hF n)

end CFSG.KS.PK

end
