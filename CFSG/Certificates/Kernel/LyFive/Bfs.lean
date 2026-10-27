module

public import CFSG.Certificates.Kernel.SporSch.LySevBfs
public import Certificates.Data.CFSGNative.LyFive.Conj
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.LyFive.Bfs

open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native
open CFSG.KS.SporSch.LySev CFSG.KS.SporSch.LyLoop CFSG.KS.SporSch.LySvB
open CFSG.RankThree.PartOne.LyFive (conjClosedOK)

@[expose] def Red (X : Array Nat) : Prop := X.size = 49 ∧ ∀ x ∈ X, x < 5

@[expose] def cj (gens : Array (Array Nat × Array Nat)) (j : Nat) (X : Array Nat) : Array Nat :=
  mul7 (mul7 gens[j]!.1 X) gens[j]!.2

theorem red_mul7 (X Y : Array Nat) : Red (mul7 X Y) := by
  refine ⟨by simp [mul7], fun x hx => ?_⟩
  unfold mul7 at hx
  rw [Array.mem_ofFn] at hx
  obtain ⟨t, rfl⟩ := hx
  exact Nat.mod_lt _ (by norm_num)

theorem get!_push_lt {α : Type} [Inhabited α] (xs : Array α) (x : α) {i : Nat}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by rw [Array.size_push]; omega), getElem!_pos xs i h,
    Array.getElem_push_lt h]

theorem get!_push_eq {α : Type} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

structure Inv (root : Array Nat) (gens : Array (Array Nat × Array Nat)) (h : Nat)
    (index : Std.HashMap (Array Nat) Nat) (pts : Array (Array Nat)) (par lab : Array Nat) : Prop where
  pos : 0 < pts.size
  zero : pts[0]! = root
  parSize : par.size = pts.size
  labSize : lab.size = pts.size
  tree : ∀ k, 1 ≤ k → k < pts.size →
    par[k]! < k ∧ lab[k]! < gens.size ∧ cj gens lab[k]! pts[par[k]!]! = pts[k]!
  inj : ∀ a < pts.size, ∀ b < pts.size, pts[a]! = pts[b]! → a = b
  idx : ∀ X, index.contains X = true ↔ ∃ k < pts.size, pts[k]! = X
  red : ∀ k < pts.size, Red pts[k]!
  done : ∀ k < pts.size, k < h → ∀ j < gens.size, ∃ k' < pts.size, pts[k']! = cj gens j pts[k]!

theorem inv_push {root : Array Nat} {gens : Array (Array Nat × Array Nat)} {h j : Nat}
    {index : Std.HashMap (Array Nat) Nat} {pts : Array (Array Nat)} {par lab : Array Nat}
    (I : Inv root gens h index pts par lab) (hh : h < pts.size) (hj : j < gens.size)
    (hy : index.contains (cj gens j pts[h]!) = false) :
    Inv root gens h (index.insert (cj gens j pts[h]!) pts.size) (pts.push (cj gens j pts[h]!))
      (par.push h) (lab.push j) := by
  set y := cj gens j pts[h]! with hydef
  have hny : ∀ k < pts.size, pts[k]! ≠ y := by
    intro k hk e
    have := (I.idx y).2 ⟨k, hk, e⟩
    rw [hy] at this
    exact absurd this (by decide)
  have hs : (pts.push y).size = pts.size + 1 := Array.size_push _
  refine ⟨by rw [hs]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [get!_push_lt _ _ I.pos, I.zero]
  · rw [Array.size_push, Array.size_push, I.parSize]
  · rw [Array.size_push, Array.size_push, I.labSize]
  · intro k hk1 hk2
    rw [hs] at hk2
    rcases Nat.lt_or_ge k pts.size with hk | hk
    · obtain ⟨a, b, c⟩ := I.tree k hk1 hk
      rw [get!_push_lt _ _ (by rw [I.parSize]; exact hk), get!_push_lt _ _ (by rw [I.labSize]; exact hk),
        get!_push_lt _ _ hk, get!_push_lt _ _ (by omega)]
      exact ⟨a, b, c⟩
    · have hk' : k = pts.size := by omega
      subst hk'
      have e1 : (par.push h)[pts.size]! = h := by rw [← I.parSize]; exact get!_push_eq _ _
      have e2 : (lab.push j)[pts.size]! = j := by rw [← I.labSize]; exact get!_push_eq _ _
      rw [e1, e2, get!_push_eq, get!_push_lt _ _ hh]
      exact ⟨hh, hj, rfl⟩
  · intro a ha b hb e
    rw [hs] at ha hb
    rcases Nat.lt_or_ge a pts.size with ha' | ha'
    · rcases Nat.lt_or_ge b pts.size with hb' | hb'
      · rw [get!_push_lt _ _ ha', get!_push_lt _ _ hb'] at e
        exact I.inj a ha' b hb' e
      · have : b = pts.size := by omega
        subst this
        rw [get!_push_lt _ _ ha', get!_push_eq] at e
        exact absurd e (hny a ha')
    · have : a = pts.size := by omega
      subst this
      rcases Nat.lt_or_ge b pts.size with hb' | hb'
      · rw [get!_push_eq, get!_push_lt _ _ hb'] at e
        exact absurd e.symm (hny b hb')
      · omega
  · intro X
    rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, I.idx X, hs]
    constructor
    · rintro (e | ⟨k, hk, e⟩)
      · exact ⟨pts.size, by omega, by rw [get!_push_eq, e]⟩
      · exact ⟨k, by omega, by rw [get!_push_lt _ _ hk, e]⟩
    · rintro ⟨k, hk, e⟩
      rcases Nat.lt_or_ge k pts.size with hk' | hk'
      · rw [get!_push_lt _ _ hk'] at e
        exact Or.inr ⟨k, hk', e⟩
      · have : k = pts.size := by omega
        subst this
        rw [get!_push_eq] at e
        exact Or.inl e
  · intro k hk
    rw [hs] at hk
    rcases Nat.lt_or_ge k pts.size with hk' | hk'
    · rw [get!_push_lt _ _ hk']
      exact I.red k hk'
    · have : k = pts.size := by omega
      subst this
      rw [get!_push_eq]
      exact red_mul7 _ _
  · intro k hk hkh j' hj'
    obtain ⟨k', hk', e⟩ := I.done k (by omega) hkh j' hj'
    exact ⟨k', by rw [hs]; omega, by rw [get!_push_lt _ _ hk', get!_push_lt _ _ (by omega), e]⟩

theorem conjBFS_inv (root : Array Nat) (gens : Array (Array Nat × Array Nat)) (cap : Nat)
    (hroot : Red root) :
    ∃ index, Inv root gens (min cap (conjBFS root gens cap).1.size) index (conjBFS root gens cap).1
      (conjBFS root gens cap).2.1 (conjBFS root gens cap).2.2 := by
  let R := fun (t : Nat) (s : Std.HashMap (Array Nat) Nat × Array (Array Nat) × Array Nat ×
      Array Nat) =>
    Inv root gens t s.1 s.2.1 s.2.2.1 s.2.2.2
  have hex : ∃ s, conjBFS root gens cap = (s.2.1, s.2.2.1, s.2.2.2) ∧ R cap s := by
    unfold conjBFS
    refine ⟨_, rfl, forIn_range_spec R cap _ _ ?_ ?_⟩
    ·
      have h0 : (#[root] : Array (Array Nat))[0]! = root := rfl
      refine ⟨Nat.one_pos, h0, rfl, rfl, fun k hk1 hk2 => ?_, fun a ha b hb _ => ?_,
        fun X => ?_, fun k hk => ?_, fun k _ hk => absurd hk (Nat.not_lt_zero k)⟩
      · change k < 1 at hk2
        omega
      · change a < 1 at ha
        change b < 1 at hb
        omega
      · change ((∅ : Std.HashMap (Array Nat) Nat).insert root 0).contains X = true ↔
          ∃ k < 1, (#[root] : Array (Array Nat))[k]! = X
        rw [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, beq_iff_eq]
        constructor
        · rintro rfl
          exact ⟨0, Nat.one_pos, h0⟩
        · rintro ⟨k, hk, e⟩
          rw [show k = 0 by omega, h0] at e
          exact e
      · change k < 1 at hk
        change Red (#[root] : Array (Array Nat))[k]!
        rw [show k = 0 by omega, h0]
        exact hroot
    ·
      intro h b _ hb
      dsimp only
      split
      · rename_i hlt
        refine ⟨_, rfl, ?_⟩
        let J := fun (j : Nat) (s : Std.HashMap (Array Nat) Nat × Array (Array Nat) ×
            Array Nat × Array Nat) =>
          Inv root gens h s.1 s.2.1 s.2.2.1 s.2.2.2 ∧ b.2.1.size ≤ s.2.1.size ∧
            (∀ k < b.2.1.size, s.2.1[k]! = b.2.1[k]!) ∧
            ∀ j' < j, ∃ k' < s.2.1.size, s.2.1[k']! = cj gens j' b.2.1[h]!
        have hfin : ∀ s, J gens.size s → R (h + 1) s := by
          rintro s ⟨I, hle, hpre, hall⟩
          refine ⟨I.pos, I.zero, I.parSize, I.labSize, I.tree, I.inj, I.idx, I.red, ?_⟩
          intro k hk hkh j hj
          rcases Nat.lt_or_ge k h with hk' | hk'
          · exact I.done k hk hk' j hj
          · have : k = h := by omega
            subst this
            rw [hpre k hlt]
            exact hall j hj
        refine hfin _ (forIn_range_spec J gens.size _ _ ⟨hb, le_rfl, fun _ _ => rfl,
          fun _ hj => absurd hj (Nat.not_lt_zero _)⟩ ?_)
        intro j s hj hs
        obtain ⟨I, hle, hpre, hall⟩ := hs
        have hx : s.2.1[h]! = b.2.1[h]! := hpre h hlt
        refine ⟨_, (apply_ite (fun z => (pure (ForInStep.yield z) : Id _)) _ _ _).symm, ?_⟩
        split
        · rename_i hnc
          have hnc' : s.1.contains (cj gens j s.2.1[h]!) = false := by
            rw [hx]
            unfold cj
            cases e : s.1.contains (mul7 (mul7 gens[j]!.1 b.2.1[h]!) gens[j]!.2)
            · rfl
            · rw [e] at hnc
              exact absurd hnc (by decide)
          have I' := inv_push I (by omega) hj hnc'
          rw [hx] at I'
          have hsz : ∀ n, n ≤ s.2.1.size → n < (s.2.1.push (cj gens j b.2.1[h]!)).size := by
            intro n hn
            rw [Array.size_push]
            omega
          refine ⟨I', Nat.le_of_lt (hsz _ hle),
            fun k hk => by rw [get!_push_lt _ _ (by omega), hpre k hk], fun j' hj' => ?_⟩
          rcases Nat.lt_or_ge j' j with h1 | h1
          · obtain ⟨k', hk', e⟩ := hall j' h1
            exact ⟨k', hsz _ (Nat.le_of_lt hk'), by rw [get!_push_lt _ _ hk', e]⟩
          · rw [show j' = j by omega]
            exact ⟨s.2.1.size, hsz _ le_rfl, get!_push_eq _ _⟩
        · rename_i hc
          refine ⟨I, hle, hpre, fun j' hj' => ?_⟩
          rcases Nat.lt_or_ge j' j with h1 | h1
          · exact hall j' h1
          · rw [show j' = j by omega]
            have hc' : s.1.contains (cj gens j b.2.1[h]!) = true := by
              unfold cj
              cases e : s.1.contains (mul7 (mul7 gens[j]!.1 b.2.1[h]!) gens[j]!.2)
              · rw [e] at hc
                exact absurd hc (by decide)
              · rfl
            exact (I.idx _).1 hc'
      · rename_i hge
        refine ⟨_, rfl, ?_⟩
        refine ⟨hb.pos, hb.zero, hb.parSize, hb.labSize, hb.tree, hb.inj, hb.idx, hb.red, ?_⟩
        intro k hk _ j hj
        change k < b.2.1.size at hk
        change ¬ h < b.2.1.size at hge
        exact hb.done k hk (by omega) j hj
  obtain ⟨s, hs, I⟩ := hex
  rw [hs]
  refine ⟨s.1, I.pos, I.zero, I.parSize, I.labSize, I.tree, I.inj, I.idx, I.red, ?_⟩
  intro k hk hkh j hj
  exact I.done k hk (Nat.lt_of_lt_of_le hkh (Nat.min_le_left _ _)) j hj

variable {root : Array Nat} {gens : Array (Array Nat × Array Nat)} {cap : Nat}

theorem conjBFS_treeOK (hroot : Red root) : conjTreeOK root gens (conjBFS root gens cap) = true := by
  obtain ⟨index, I⟩ := conjBFS_inv root gens cap hroot
  set T := conjBFS root gens cap
  unfold conjTreeOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨I.parSize, I.labSize⟩, I.zero⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    have hr := I.red i hi
    rw [getElem!_pos T.1 i hi] at hr
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
    exact ⟨hr.1, fun r hr' => hr.2 _ (Array.getElem_mem hr')⟩
  · rw [allIn_iff']
    intro k hk1 hk2
    obtain ⟨a, b, c⟩ := I.tree k hk1 hk2
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨a, b⟩, c⟩
  · rw [allIn_iff']
    intro k _ hk2
    rw [beq_iff_eq]
    exact index_getD _ I.inj hk2

theorem conjBFS_mem (hroot : Red root) (P : Array Nat → Prop) (h0 : P root)
    (hstep : ∀ X j, j < gens.size → P X → P (cj gens j X)) :
    ∀ k < (conjBFS root gens cap).1.size, P (conjBFS root gens cap).1[k]! := by
  obtain ⟨index, I⟩ := conjBFS_inv root gens cap hroot
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [I.zero]
      exact h0
    · obtain ⟨a, b, c⟩ := I.tree k hpos hk
      rw [← c]
      exact hstep _ _ b (ih _ a (by omega))

theorem conjBFS_inj (hroot : Red root) :
    ∀ a < (conjBFS root gens cap).1.size, ∀ b < (conjBFS root gens cap).1.size,
      (conjBFS root gens cap).1[a]! = (conjBFS root gens cap).1[b]! → a = b :=
  (conjBFS_inv root gens cap hroot).choose_spec.inj

theorem conjBFS_red (hroot : Red root) :
    ∀ k < (conjBFS root gens cap).1.size, Red (conjBFS root gens cap).1[k]! :=
  (conjBFS_inv root gens cap hroot).choose_spec.red

theorem conjBFS_pos (hroot : Red root) : 0 < (conjBFS root gens cap).1.size :=
  (conjBFS_inv root gens cap hroot).choose_spec.pos

theorem conjBFS_zero (hroot : Red root) : (conjBFS root gens cap).1[0]! = root :=
  (conjBFS_inv root gens cap hroot).choose_spec.zero

theorem conjBFS_closed (hroot : Red root) (hcap : (conjBFS root gens cap).1.size ≤ cap) :
    ∀ k < (conjBFS root gens cap).1.size, ∀ j < gens.size,
      ∃ k' < (conjBFS root gens cap).1.size,
        (conjBFS root gens cap).1[k']! = cj gens j (conjBFS root gens cap).1[k]! := by
  obtain ⟨index, I⟩ := conjBFS_inv root gens cap hroot
  intro k hk j hj
  exact I.done k hk (by rw [Nat.min_eq_right hcap]; exact hk) j hj

theorem conjBFS_closedOK (hroot : Red root) (hcap : (conjBFS root gens cap).1.size ≤ cap) :
    conjClosedOK gens (conjBFS root gens cap) = true := by
  have hc := conjBFS_closed hroot hcap
  have hinj := conjBFS_inj (gens := gens) (cap := cap) hroot
  set T := conjBFS root gens cap
  unfold conjClosedOK
  dsimp only
  rw [allIn_iff']
  intro k _ hk
  rw [Array.all_eq_true]
  intro j hj
  obtain ⟨k', hk', e⟩ := hc k hk j hj
  have hg : gens[j] = gens[j]! := (getElem!_pos gens j hj).symm
  rw [hg]
  change ((List.range T.1.size).foldl (fun (m : Std.HashMap (Array Nat) Nat) k => m.insert T.1[k]! k)
    ∅).contains (cj gens j T.1[k]!) = true
  rw [← e, Std.HashMap.contains_eq_isSome_getElem?, index_fold T.1 T.1.size hinj k' hk']
  rfl

end CFSG.KS.LyFive.Bfs

end
