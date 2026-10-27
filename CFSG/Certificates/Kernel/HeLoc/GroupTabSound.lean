module

public import CFSG.RankThree.PartOne.KS.PKitSimple
public import CFSG.Certificates.Kernel.MonsterB.BfsCore
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.KC.HeLoc

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartOne

variable {n : Nat}

@[expose] def classRepsI (N id0 : Nat) (cj : Nat → Nat → Nat) : List Nat :=
  (List.range N).foldl (fun reps k =>
    if (k == id0 || reps.any fun r => (List.range N).any fun j => k == cj j r) then reps
    else reps ++ [k]) []

theorem foldl_congr_lt {N : Nat} {f g : List Nat → Nat → List Nat}
    (hfg : ∀ reps k, (∀ r ∈ reps, r < N) → k < N → f reps k = g reps k)
    (hg : ∀ reps k, (∀ r ∈ reps, r < N) → k < N → ∀ r ∈ g reps k, r < N) :
    ∀ (l : List Nat), (∀ k ∈ l, k < N) → ∀ reps, (∀ r ∈ reps, r < N) →
      l.foldl f reps = l.foldl g reps
  | [], _, _, _ => rfl
  | k :: l, hl, reps, hr => by
    rw [List.foldl_cons, List.foldl_cons, hfg reps k hr (hl k List.mem_cons_self)]
    exact foldl_congr_lt hfg hg l (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')) _
      (hg reps k hr (hl k List.mem_cons_self))

theorem any_congr_mem {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem classReps_eq {c : CFSG.Monster.B.Fischer.ArrCert} {N id0 : Nat} {cj : Nat → Nat → Nat}
    (hN : c.pts.size = N) (hid : ∀ k < N, eqA n c.pts[k]! (idA n) = (k == id0))
    (hcj : ∀ k < N, ∀ j < N, ∀ r < N, eqA n c.pts[k]! (conjA n c.pts[j]! c.pts[r]!) = (k == cj j r)) :
    classReps n c = classRepsI N id0 cj := by
  unfold classReps classRepsI
  rw [hN]
  refine foldl_congr_lt (N := N) (fun reps k hr hk => ?_) (fun reps k hr hk r hrm => ?_)
    (List.range N) (fun k hk => List.mem_range.1 hk) [] (by simp)
  · have e : (reps.any fun r => (List.range N).any fun j => eqA n c.pts[k]! (conjA n c.pts[j]! c.pts[r]!)) =
        (reps.any fun r => (List.range N).any fun j => k == cj j r) := by
      refine any_congr_mem _ _ _ fun r hr' => any_congr_mem _ _ _ fun j hj => ?_
      exact hcj k hk j (List.mem_range.1 hj) r (hr r hr')
    rw [hid k hk, e]
  · split at hrm
    · exact hr r hrm
    · rw [List.mem_append, List.mem_singleton] at hrm
      rcases hrm with h | rfl
      · exact hr r h
      · exact hk

theorem reach_of_tree {gs : Array (Array Nat)} {U : Nat → Array Nat} {N : Nat}
    {par lab dep : Nat → Nat} (h0 : U 0 = idA n)
    (ht : ∀ i < N, i = 0 ∨ (par i < N ∧ lab i < gs.size ∧ dep i = dep (par i) + 1 ∧
      U i = compA n gs[lab i]! (U (par i)))) :
    ∀ i < N, CFSG.KC.Bfs.Reach (leftA n gs) gs.size (idA n) (U i) := by
  suffices H : ∀ d, ∀ i < N, dep i = d → CFSG.KC.Bfs.Reach (leftA n gs) gs.size (idA n) (U i) from
    fun i hi => H _ i hi rfl
  intro d
  induction d with
  | zero =>
    intro i hi hd
    rcases ht i hi with rfl | ⟨_, _, hdp, _⟩
    · rw [h0]
      exact CFSG.KC.Bfs.Reach.root
    · omega
  | succ d ih =>
    intro i hi hd
    rcases ht i hi with rfl | ⟨hp, hl, hdp, he⟩
    · rw [h0]
      exact CFSG.KC.Bfs.Reach.root
    · rw [he]
      exact CFSG.KC.Bfs.Reach.step (lab i) hl (ih (par i) hp (by omega))

end CFSG.KC.HeLoc

end
