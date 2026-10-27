module

public import CFSG.Certificates.Kernel.Spor.HBfsReplay

public section

namespace CFSG.KS.HBfs

open CFSG.KS.BfsReplay

variable {α : Type} [Inhabited α] {key : α → UInt64} {step : Nat → α → α} {k : Nat} {root : α}

def TreeInv (step : Nat → α → α) (k : Nat) (root : α) (s : HSt α) : Prop :=
  s.2.2.1.size = s.2.1.size ∧ s.2.2.2.size = s.2.1.size ∧ 0 < s.2.1.size ∧ s.2.1[0]! = root ∧
    ∀ i, 0 < i → i < s.2.1.size →
      s.2.2.1[i]! < i ∧ s.2.2.2[i]! < k ∧ s.2.1[i]! = step s.2.2.2[i]! s.2.1[s.2.2.1[i]!]!

theorem treeInv_inner {h : Nat} {s : HSt α} (hI : TreeInv step k root s) (hh : h < s.2.1.size) :
    TreeInv step k root (Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (hInner key step s.2.1[h]! h))) := by
  have := forIn_range'_yield k 0 (s.1, s.2.1, s.2.2.1, s.2.2.2) (hInner key step s.2.1[h]! h)
    (fun j s' => TreeInv step k root s' ∧ s.2.1.size ≤ s'.2.1.size ∧
      ∀ i < s.2.1.size, s'.2.1[i]! = s.2.1[i]!)
    (fun j hj s' hP => ?_) ⟨hI, Nat.le_refl _, fun _ _ => rfl⟩
  · exact this.1
  · obtain ⟨⟨a1, a2, a3, a4, a5⟩, hle, hfix⟩ := hP
    rw [Nat.zero_add]
    unfold hInner
    split
    · refine ⟨_, rfl, ⟨by simp [a1], by simp [a2], by simp, ?_, fun i h0 hi => ?_⟩, by simp; omega,
        fun i hi => ?_⟩
      · change (s'.2.1.push _)[0]! = root
        rw [push_lt a3, a4]
      · change (s'.2.2.1.push h)[i]! < i ∧ (s'.2.2.2.push j)[i]! < k ∧
          (s'.2.1.push _)[i]! = step (s'.2.2.2.push j)[i]! (s'.2.1.push _)[(s'.2.2.1.push h)[i]!]!
        have hi' : i < s'.2.1.size + 1 := by simpa using hi
        rcases Nat.lt_or_ge i s'.2.1.size with b | b
        · rw [push_lt (by omega), push_lt (by omega), push_lt b]
          obtain ⟨c1, c2, c3⟩ := a5 i h0 b
          rw [push_lt (by omega)]
          exact ⟨c1, c2, c3⟩
        · have e : i = s'.2.1.size := by omega
          rw [e]
          have p1 : (s'.2.2.1.push h)[s'.2.1.size]! = h := by
            rw [← a1]
            exact push_eq
          have p2 : (s'.2.2.2.push j)[s'.2.1.size]! = j := by
            rw [← a2]
            exact push_eq
          rw [p1, p2, push_eq, push_lt (by omega : h < s'.2.1.size), hfix h hh]
          exact ⟨by omega, hj, rfl⟩
      · change (s'.2.1.push _)[i]! = _
        rw [push_lt (by omega), hfix i hi]
    · exact ⟨_, rfl, ⟨a1, a2, a3, a4, a5⟩, hle, hfix⟩

theorem treeInv_outer (cap : Nat) :
    TreeInv step k root (Id.run (forIn (List.range' 0 cap) (hInit key root) (hOuter key step k))) := by
  refine forIn_range'_done cap 0 (hInit key root) (hOuter key step k)
    (fun _ s => TreeInv step k root s) (TreeInv step k root) (fun h _ s hP => ?_) (fun _ hb => hb) ?_
  · rw [Nat.zero_add]
    by_cases hh : h < s.2.1.size
    · refine Or.inl ⟨_, ?_, treeInv_inner (key := key) hP hh⟩
      unfold hOuter
      rw [ite_eq_left hh]
    · refine Or.inr ⟨_, ?_, hP⟩
      unfold hOuter
      rw [ite_eq_right hh]
  · refine ⟨rfl, rfl, by simp [hInit], rfl, fun i h0 hi => ?_⟩
    simp [hInit] at hi
    omega

theorem hbfs_tree (key : α → UInt64) (step : Nat → α → α) (k : Nat) (root : α) (cap : Nat) :
    0 < (hbfs key step k root cap).1.size ∧ (hbfs key step k root cap).1[0]! = root ∧
      (hbfs key step k root cap).2.1.size = (hbfs key step k root cap).1.size ∧
      (hbfs key step k root cap).2.2.size = (hbfs key step k root cap).1.size ∧
      ∀ i, 0 < i → i < (hbfs key step k root cap).1.size →
        (hbfs key step k root cap).2.1[i]! < i ∧ (hbfs key step k root cap).2.2[i]! < k ∧
        (hbfs key step k root cap).1[i]! = step (hbfs key step k root cap).2.2[i]!
          (hbfs key step k root cap).1[(hbfs key step k root cap).2.1[i]!]! := by
  have hT := treeInv_outer (key := key) (step := step) (k := k) (root := root) cap
  rw [hbfs_eq]
  generalize Id.run (forIn (List.range' 0 cap) (hInit key root) (hOuter key step k)) = s at hT
  obtain ⟨a1, a2, a3, a4, a5⟩ := hT
  exact ⟨a3, a4, a1, a2, a5⟩

end CFSG.KS.HBfs

end
