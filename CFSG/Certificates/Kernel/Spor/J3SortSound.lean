module

public import Certificates.Data.CFSGNative.J3.Basic
import CFSG.Certificates.Kernel.Spor.TBfsSound
import CFSG.Certificates.Kernel.Common.QSort

public section

namespace CFSG.KS.J3Sort

open CFSG.Sporadic.J3.Native

abbrev St := Std.HashMap Nat Unit × Array Nat

@[expose] def oBody (d : Nat) (cA cB : Array Nat) (h : Nat) (s : St) : Id (ForInStep St) :=
  if h < s.snd.size then
    if (!s.fst.contains (vecMulN d cA s.snd[h]!)) = true then
      if (!(s.fst.insert (vecMulN d cA s.snd[h]!) ()).contains (vecMulN d cB s.snd[h]!)) = true then
        pure (ForInStep.yield
          ((s.fst.insert (vecMulN d cA s.snd[h]!) ()).insert (vecMulN d cB s.snd[h]!) (),
            (s.snd.push (vecMulN d cA s.snd[h]!)).push (vecMulN d cB s.snd[h]!)))
      else
        pure (ForInStep.yield
          (s.fst.insert (vecMulN d cA s.snd[h]!) (), s.snd.push (vecMulN d cA s.snd[h]!)))
    else
      if (!s.fst.contains (vecMulN d cB s.snd[h]!)) = true then
        pure (ForInStep.yield
          (s.fst.insert (vecMulN d cB s.snd[h]!) (), s.snd.push (vecMulN d cB s.snd[h]!)))
      else pure (ForInStep.yield (s.fst, s.snd))
  else pure (ForInStep.done (s.fst, s.snd))

theorem orbitSorted_eq (d : Nat) (cA cB : Array Nat) (v0 cap : Nat) :
    orbitSorted d cA cB v0 cap = (Id.run (forIn (List.range' 0 cap)
      (((Std.HashMap.emptyWithCapacity (2 * cap)).insert v0 (), #[v0]) : St)
      (oBody d cA cB))).2.qsort (fun x1 x2 => decide (x1 < x2)) := by
  unfold orbitSorted
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

@[expose] def addP (s : St) (w : Nat) : St :=
  if (!s.1.contains w) = true then (s.1.insert w (), s.2.push w) else s

theorem oBody_lt {d : Nat} {cA cB : Array Nat} {h : Nat} {s : St} (hh : h < s.2.size) :
    oBody d cA cB h s = pure (ForInStep.yield
      (addP (addP s (vecMulN d cA s.2[h]!)) (vecMulN d cB s.2[h]!))) := by
  unfold oBody addP
  simp only [hh, ↓reduceIte]
  by_cases c1 : (!s.fst.contains (vecMulN d cA s.snd[h]!)) = true
  · by_cases c2 : (!(s.fst.insert (vecMulN d cA s.snd[h]!) ()).contains
        (vecMulN d cB s.snd[h]!)) = true
    · simp only [c1, c2, ↓reduceIte]
    · simp only [c1, c2, Bool.false_eq_true, ↓reduceIte]
  · by_cases c2 : (!s.fst.contains (vecMulN d cB s.snd[h]!)) = true
    · simp only [c1, c2, Bool.false_eq_true, ↓reduceIte]
    · simp only [c1, c2, Bool.false_eq_true, ↓reduceIte]

theorem oBody_ge {d : Nat} {cA cB : Array Nat} {h : Nat} {s : St} (hh : ¬ h < s.2.size) :
    oBody d cA cB h s = pure (ForInStep.done s) := by
  unfold oBody
  simp only [hh, ↓reduceIte]

structure Good (S : Nat → Prop) (s : St) : Prop where
  nodup : s.2.toList.Nodup
  inS : ∀ x ∈ s.2, S x
  seen : ∀ x, s.1.contains x = true ↔ x ∈ s.2

theorem addP_spec {S : Nat → Prop} {s : St} {w : Nat} (hg : Good S s) (hw : S w) :
    Good S (addP s w) ∧ w ∈ (addP s w).2 ∧ s.2.size ≤ (addP s w).2.size ∧
      ∀ h < s.2.size, (addP s w).2[h]! = s.2[h]! := by
  unfold addP
  by_cases c : s.1.contains w = true
  · have : ¬ ((!s.1.contains w) = true) := by simp [c]
    simp only [this]
    exact ⟨hg, (hg.seen w).1 c, Nat.le_refl _, fun _ _ => rfl⟩
  · have c' : (!s.1.contains w) = true := by simpa using c
    simp only [c', ↓reduceIte]
    have hnw : w ∉ s.2 := fun hm => c ((hg.seen w).2 hm)
    refine ⟨⟨?_, fun x hx => ?_, fun x => ?_⟩, by simp, by simp, fun h hh => TBfs.push_lt hh⟩
    · rw [Array.toList_push, List.nodup_append]
      refine ⟨hg.nodup, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      intro e
      subst e
      exact hnw (Array.mem_def.2 ha)
    · rcases Array.mem_push.1 hx with hx | rfl
      · exact hg.inS x hx
      · exact hw
    · rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, Array.mem_push, hg.seen x]
      constructor
      · rintro (e | e)
        · exact Or.inr e.symm
        · exact Or.inl e
      · rintro (e | e)
        · exact Or.inr e
        · exact Or.inl e.symm

theorem mem_of_ext {s s' : Array Nat} (hle : s.size ≤ s'.size)
    (hg : ∀ h < s.size, s'[h]! = s[h]!) {x : Nat} (hx : x ∈ s) : x ∈ s' := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  have := hg i hi
  rw [getElem!_pos s' i (by omega), getElem!_pos s i hi] at this
  rw [← this]
  exact Array.getElem_mem _

structure Inv (d : Nat) (cA cB : Array Nat) (S : Nat → Prop) (v0 j : Nat) (s : St) : Prop where
  good : Good S s
  root : v0 ∈ s.2
  le : j ≤ s.2.size
  cl : ∀ h < j, vecMulN d cA s.2[h]! ∈ s.2 ∧ vecMulN d cB s.2[h]! ∈ s.2

structure Fin' (d : Nat) (cA cB : Array Nat) (S : Nat → Prop) (v0 n : Nat) (s : St) : Prop where
  good : Good S s
  root : v0 ∈ s.2
  cl : n ≤ s.2.size ∨ ∀ x ∈ s.2, vecMulN d cA x ∈ s.2 ∧ vecMulN d cB x ∈ s.2

theorem bfs_final {d n : Nat} {cA cB : Array Nat} {S : Nat → Prop} {v0 : Nat}
    (hS : ∀ x, S x → S (vecMulN d cA x) ∧ S (vecMulN d cB x)) (h0 : S v0) :
    Fin' d cA cB S v0 n (Id.run (forIn (List.range' 0 n)
      (((Std.HashMap.emptyWithCapacity (2 * n)).insert v0 (), #[v0]) : St)
      (oBody d cA cB))) := by
  refine TBfs.forIn_range'_done n 0 _ _ (fun j s => Inv d cA cB S v0 j s) (Fin' d cA cB S v0 n)
    (fun j _ s J => ?_) (fun s J => ⟨J.good, J.root, Or.inl J.le⟩) ?_
  · rw [Nat.zero_add]
    by_cases hj : j < s.2.size
    · left
      refine ⟨_, oBody_lt hj, ?_⟩
      have hv : s.2[j]! ∈ s.2 := by
        rw [getElem!_pos s.2 j hj]
        exact Array.getElem_mem _
      have hSv := hS _ (J.good.inS _ hv)
      obtain ⟨g1, m1, l1, e1⟩ := addP_spec J.good hSv.1
      obtain ⟨g2, m2, l2, e2⟩ := addP_spec g1 hSv.2
      have mono : ∀ x ∈ s.2, x ∈ (addP (addP s (vecMulN d cA s.2[j]!)) (vecMulN d cB s.2[j]!)).2 :=
        fun x hx => mem_of_ext l2 e2 (mem_of_ext l1 e1 hx)
      have eg : ∀ h < s.2.size,
          (addP (addP s (vecMulN d cA s.2[j]!)) (vecMulN d cB s.2[j]!)).2[h]! = s.2[h]! :=
        fun h hh => by rw [e2 h (by omega), e1 h hh]
      refine ⟨g2, mono _ J.root, by omega, fun h hh => ?_⟩
      rw [eg h (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | rfl
      · exact ⟨mono _ (J.cl h hh).1, mono _ (J.cl h hh).2⟩
      · exact ⟨mem_of_ext l2 e2 m1, m2⟩
    · right
      refine ⟨s, oBody_ge hj, J.good, J.root, Or.inr fun x hx => ?_⟩
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
      have := J.cl i (by have := J.le; omega)
      rw [getElem!_pos s.2 i hi] at this
      exact this
  · refine ⟨⟨by simp, fun x hx => ?_, fun x => ?_⟩, by simp, by simp, fun h hh => by omega⟩
    · rw [List.mem_toArray, List.mem_singleton] at hx
      rw [hx]
      exact h0
    · rw [Std.HashMap.contains_insert, Std.HashMap.contains_emptyWithCapacity, Bool.or_false,
        beq_iff_eq, List.mem_toArray, List.mem_singleton]
      exact ⟨fun e => e.symm, fun e => e.symm⟩

theorem posMap_get {pts : Array Nat}
    (hinj : ∀ i < pts.size, ∀ j < pts.size, pts[i]! = pts[j]! → i = j) :
    ∀ i < pts.size, (posMap pts).get? pts[i]! = some i := by
  have heq : posMap pts = (List.range pts.size).foldl (fun m i => m.insert pts[i]! i)
      (Std.HashMap.emptyWithCapacity (2 * pts.size)) := by
    unfold posMap
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl, List.range_eq_range']
  have step : ∀ m ≤ pts.size, ∀ i < m,
      ((List.range m).foldl (fun m i => m.insert pts[i]! i)
        (Std.HashMap.emptyWithCapacity (2 * pts.size) : Std.HashMap Nat Nat))[pts[i]!]? =
          some i := by
    intro m
    induction m with
    | zero => intro _ i hi; omega
    | succ m ih =>
      intro hm i hi
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Std.HashMap.getElem?_insert]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · have hne : (pts[m]! == pts[i]!) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          have := hinj m (by omega) i (by omega) e
          omega
        rw [hne]
        exact ih (by omega) i hi
      · simp
  intro i hi
  rw [heq, Std.HashMap.get?_eq_getElem?]
  exact step pts.size (Nat.le_refl _) i hi

theorem orbit_core {d n : Nat} {cA cB : Array Nat} {v0 : Nat} {PL TA TB BO BOI BQ : Nat → Nat}
    (hn : 0 < n)
    (hinc : ∀ i, i + 1 < n → PL i < PL (i + 1))
    (hpt : ∀ i < n, TA i < n ∧ TB i < n ∧ vecMulN d cA (PL i) = PL (TA i) ∧
      vecMulN d cB (PL i) = PL (TB i))
    (hroot : BO 0 < n ∧ PL (BO 0) = v0)
    (hbo : ∀ i < n, BOI i < n ∧ BO (BOI i) = i)
    (hbfs : ∀ k < n, 0 < k → BO k < n ∧ BQ k < k ∧
      (BO k = TA (BO (BQ k)) ∨ BO k = TB (BO (BQ k)))) :
    orbitSorted d cA cB v0 n = Array.ofFn (n := n) (fun i => PL i.val) ∧
      imageTable d (posMap (Array.ofFn (n := n) fun i => PL i.val))
        (Array.ofFn (n := n) fun i => PL i.val) cA =
          Array.ofFn (n := n) (fun i => UInt32.ofNat (TA i.val)) ∧
      imageTable d (posMap (Array.ofFn (n := n) fun i => PL i.val))
        (Array.ofFn (n := n) fun i => PL i.val) cB =
          Array.ofFn (n := n) (fun i => UInt32.ofNat (TB i.val)) := by
  have hmono : ∀ i j, i < j → j < n → PL i < PL j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact Nat.lt_trans (ih h (by omega)) (hinc j hj)
      · exact hinc i hj
  have hinj : ∀ i < n, ∀ j < n, PL i = PL j → i = j := by
    intro i hi j hj e
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := hmono i j h hj
      omega
    · exact h
    · have := hmono j i h hi
      omega
  let P := Array.ofFn (n := n) fun i => PL i.val
  have hP : ∀ i < n, P[i]! = PL i := fun i hi => by
    rw [getElem!_pos P i (by simp [P]; omega), Array.getElem_ofFn]
  let S : Nat → Prop := fun x => ∃ i < n, PL i = x
  have hS : ∀ x, S x → S (vecMulN d cA x) ∧ S (vecMulN d cB x) := by
    rintro x ⟨i, hi, rfl⟩
    obtain ⟨a1, a2, a3, a4⟩ := hpt i hi
    exact ⟨⟨TA i, a1, a3.symm⟩, ⟨TB i, a2, a4.symm⟩⟩
  rw [orbitSorted_eq]
  have F := bfs_final (n := n) (d := d) (cA := cA) (cB := cB) hS ⟨BO 0, hroot.1, hroot.2⟩
  generalize Id.run (forIn (List.range' 0 n)
    (((Std.HashMap.emptyWithCapacity (2 * n)).insert v0 (), #[v0]) : St)
    (oBody d cA cB)) = s at F ⊢
  have hSl : (List.ofFn (n := n) fun i => PL i.val).Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    simp only [List.length_ofFn] at hj
    exact hmono i j hij hj
  have memSl : ∀ x, x ∈ (List.ofFn (n := n) fun i => PL i.val) ↔ S x := by
    intro x
    rw [List.mem_ofFn]
    exact ⟨fun ⟨i, e⟩ => ⟨i.val, i.isLt, e⟩, fun ⟨i, hi, e⟩ => ⟨⟨i, hi⟩, e⟩⟩
  have hall : ∀ x, S x → x ∈ s.2 := by
    rcases F.cl with hle | hcl
    · intro x hx
      refine Classical.byContradiction fun hm => ?_
      have hsub : s.2.toList ⊆ (List.ofFn (n := n) fun i => PL i.val).erase x := by
        intro y hy
        have hyx : y ≠ x := fun e => hm (by rw [← e]; exact Array.mem_def.2 hy)
        exact (List.mem_erase_of_ne hyx).2 ((memSl y).2 (F.good.inS y (Array.mem_def.2 hy)))
      have := F.good.nodup.length_le_of_subset hsub
      rw [List.length_erase_of_mem ((memSl x).2 hx), List.length_ofFn, Array.length_toList] at this
      omega
    · have reach : ∀ k < n, PL (BO k) ∈ s.2 := by
        intro k
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro hk
          rcases Nat.eq_zero_or_pos k with rfl | hk0
          · rw [hroot.2]
            exact F.root
          · obtain ⟨b1, b2, b3⟩ := hbfs k hk hk0
            have hq := ih (BQ k) b2 (by omega)
            have hqn : BO (BQ k) < n := by
              rcases Nat.eq_zero_or_pos (BQ k) with e | e
              · rw [e]
                exact hroot.1
              · exact (hbfs (BQ k) (by omega) e).1
            obtain ⟨a1, a2, a3, a4⟩ := hpt _ hqn
            rcases b3 with e | e
            · rw [e, ← a3]
              exact (hcl _ hq).1
            · rw [e, ← a4]
              exact (hcl _ hq).2
      rintro x ⟨i, hi, rfl⟩
      rw [← (hbo i hi).2]
      exact reach _ (hbo i hi).1
  have hperm : s.2.toList.Perm (List.ofFn (n := n) fun i => PL i.val) := by
    rw [List.perm_ext_iff_of_nodup F.good.nodup (List.nodup_iff_pairwise_ne.2
      (hSl.imp fun h e => by omega))]
    intro x
    rw [memSl]
    exact ⟨fun hx => F.good.inS x (Array.mem_def.2 hx), fun hx => Array.mem_def.1 (hall x hx)⟩
  refine ⟨?_, ?_, ?_⟩
  · apply Array.toList_inj.1
    rw [Array.toList_ofFn]
    have hq := Array.perm_iff_toList_perm.1 (CFSG.KC.QSort.qsort_perm s.2 fun x1 x2 => decide (x1 < x2))
    have hs := CFSG.KC.QSort.qsort_pairwise s.2 (fun x1 x2 => decide (x1 < x2))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at h1 h2 ⊢; omega)
      (fun a b h1 => by simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h1 ⊢; omega)
    refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h1 h2 => by omega)
      (hs.imp fun h => by simp only [decide_eq_false_iff_not] at h; omega)
      (hSl.imp fun h => by omega) (hq.trans hperm)
  all_goals
    have hPs : P.size = n := by simp [P]
    have hpos := posMap_get (pts := P) (fun i hi j hj e => by
      rw [hPs] at hi hj
      rw [hP i hi, hP j hj] at e
      exact hinj i hi j hj e)
    apply Array.ext (by simp [imageTable])
    intro i h1 h2
    simp only [imageTable, Array.getElem_map, Array.getElem_ofFn]
    have hi : i < n := by simpa using h2
    obtain ⟨a1, a2, a3, a4⟩ := hpt i hi
  · rw [a3, ← hP _ a1, hpos _ (by rw [hPs]; exact a1)]
    rfl
  · rw [a4, ← hP _ a2, hpos _ (by rw [hPs]; exact a2)]
    rfl

end CFSG.KS.J3Sort

end
