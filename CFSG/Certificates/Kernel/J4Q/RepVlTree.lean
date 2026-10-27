module

public import CFSG.Sporadic.J4.QT2LocVLNative
import CFSG.Certificates.Kernel.J4Q.ConjBFS

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem vlTree_sound {seeds : List (List Nat)} {fuel n s : Nat} {TS : Nat → List Nat}
    {PAR LAB : Nat → Nat} {TT : Nat → Nat → Nat}
    (_hseeds : seeds.eraseDups = (List.range s).map TS) (_hsn : s ≤ n)
    (_hdist : ∀ i < n, ∀ j < n, TS i = TS j → i = j)
    (_htree : ∀ k, s ≤ k → k < n → PAR k < k ∧ LAB k < 6 ∧
      TS k = letConj (letters.getD (LAB k) 0) (TS (PAR k)))
    (_hclos : ∀ k < n, ∀ g < 6, TT k g < n ∧ letConj (letters.getD g 0) (TS k) = TS (TT k g))
    (_hord : ∀ k, s ≤ k → k + 1 < n → PAR k * 6 + LAB k < PAR (k + 1) * 6 + LAB (k + 1))
    (_hfirst : ∀ k < n, ∀ g < 6, TT k g < s ∨ PAR (TT k g) * 6 + LAB (TT k g) ≤ k * 6 + g)
    (_hfuel : n ≤ fuel) :
    (vlTree seeds fuel).toList = (List.range n).map fun k =>
      (TS k, if k < s then 0 else PAR k, if k < s then 0 else letters.getD (LAB k) 0) := by
  rw [ConjBFS.vlTree_eq, ConjBFS.gbfs_sound (key := (·.1)) (mkSeed := fun s => (s, 0, 0))
    (mkNew := fun u i ℓ => (u, i, ℓ)) (fun _ => rfl) (fun _ _ _ => rfl) _hseeds _hsn _hdist _htree
    _hclos _hord _hfirst _hfuel]
  apply List.map_congr_left
  intro k _
  unfold ConjBFS.entry
  split <;> rfl

theorem vlNodeMap_sound {L : List (List Nat × Nat × Int)} (_hL : vlInvTree.toList = L)
    (_hd : (L.map Prod.fst).Nodup) {k : Nat} (_hk : k < L.length) :
    vlNodeMap.get? (L[k].1) = some k := by
  subst _hL
  have hsz : vlInvTree.toList.length = vlInvTree.size := Array.length_toList
  have hinj : ∀ i (hi : i < vlInvTree.toList.length) j (hj : j < vlInvTree.toList.length),
      vlInvTree.toList[i].1 = vlInvTree.toList[j].1 → i = j := by
    intro i hi j hj h
    have hp := List.pairwise_iff_getElem.1 _hd
    have hi' : i < (vlInvTree.toList.map Prod.fst).length := by rw [List.length_map]; exact hi
    have hj' : j < (vlInvTree.toList.map Prod.fst).length := by rw [List.length_map]; exact hj
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact absurd (by rw [List.getElem_map, List.getElem_map]; exact h) (hp i j hi' hj' hij)
    · exact hij
    · exact absurd (by rw [List.getElem_map, List.getElem_map]; exact h.symm) (hp j i hj' hi' hij)
  have hget : ∀ j (hj : j < vlInvTree.size), (vlInvTree[j]!).1 = vlInvTree.toList[j].1 := by
    intro j hj
    rw [getElem!_pos vlInvTree j hj, Array.getElem_toList]
  let I : Nat → Std.HashMap (List Nat) Nat → Prop := fun q m =>
    (∀ i (hi : i < q) (hl : i < vlInvTree.toList.length), m[vlInvTree.toList[i].1]? = some i) ∧
      ∀ x, m.contains x = true → ∃ i, ∃ (hi : i < q) (hl : i < vlInvTree.toList.length),
        vlInvTree.toList[i].1 = x
  let P : Std.HashMap (List Nat) Nat → Prop := fun m => m.get? (vlInvTree.toList[k].1) = some k
  change P vlNodeMap
  unfold vlNodeMap
  refine BfsOrder.forIn_range_bind I P _ _ _ _ (fun q m hq hI => ?_) (fun m hI => ?_) ⟨?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hI
    have hql : q < vlInvTree.toList.length := by omega
    have hnc : m.contains vlInvTree.toList[q].1 = false := by
      cases e : m.contains vlInvTree.toList[q].1
      · rfl
      · obtain ⟨i, hi, hl, hx⟩ := h2 _ e
        have := hinj i hl q hql hx
        omega
    dsimp only
    rw [hget q hq, hnc]
    refine ⟨fun i hi hl => ?_, fun x hx => ?_⟩
    · rw [Std.HashMap.getElem?_insert]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · have hne : (vlInvTree.toList[q].1 == vlInvTree.toList[i].1) = false := by
          cases e : (vlInvTree.toList[q].1 == vlInvTree.toList[i].1)
          · rfl
          · have := hinj q hql i hl (beq_iff_eq.1 e)
            omega
        rw [hne]
        exact h1 i hi hl
      · simp
    · rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with hx | hx
      · exact ⟨q, Nat.lt_succ_self q, hql, hx⟩
      · obtain ⟨i, hi, hl, hx⟩ := h2 x hx
        exact ⟨i, by omega, hl, hx⟩
  · change m.get? (vlInvTree.toList[k].1) = some k
    rw [Std.HashMap.get?_eq_getElem?]
    exact hI.1 k (by omega) _hk
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro x hx
    simp at hx

end CFSG.KC.J4Q

end
