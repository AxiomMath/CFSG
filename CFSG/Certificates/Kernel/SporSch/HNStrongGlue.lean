
module

public import CFSG.Sporadic.HNSchreier.InvolCheckInputs

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

theorem mword_congr {S Si S' Si' : Array (Array (Array Nat))} {j : Nat}
    (hS : ∀ i < j, S[i]! = S'[i]!) (hSi : ∀ i < j, Si[i]! = Si'[i]!) :
    ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j) → mword S Si w = mword S' Si' w
  | [], _ => rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    rw [mword, mword, mword_congr hS hSi w fun l' h' => hw l' (List.mem_cons_of_mem _ h'),
      mletter, mletter]
    by_cases hpos : 0 < l
    · rw [if_pos hpos, if_pos hpos, hS _ (by omega)]
    · rw [if_neg hpos, if_neg hpos, hSi _ (by omega)]

theorem ofFn_getElem! {α : Type} [Inhabited α] {n i : Nat} {F : Nat → α} (hi : i < n) :
    (Array.ofFn (n := n) fun k => F k.val)[i]! = F i := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

@[expose] def ExtM (F FI : Nat → Array (Array Nat)) (k : Nat)
    (p : Array (Array (Array Nat)) × Array (Array (Array Nat))) : Prop :=
  p.1.size = k ∧ p.2.size = k ∧ ∀ i < k, p.1[i]! = F i ∧ p.2[i]! = FI i

theorem extendStrongM_eq {orig : Array (Array (Array Nat))} {W : Array (List Int)} {s : Nat}
    {F FI : Nat → Array (Array Nat)} (hm : orig.size = 2) (hs : W.size = s) (h2 : 2 ≤ s)
    (hO : ∀ j < 2, orig[j]! = F j) (hinv : ∀ j < s, invM 5 133 (F j) = FI j)
    (hW : ∀ j, 2 ≤ j → j < s → (∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      mword (Array.ofFn (n := s) fun i => F i.val) (Array.ofFn (n := s) fun i => FI i.val) W[j]! =
        F j) :
    extendStrongM orig W =
      (Array.ofFn (n := s) fun i => F i.val, Array.ofFn (n := s) fun i => FI i.val) := by
  have step : ∀ k, 2 + k < s → ∀ p, ExtM F FI (2 + k) p →
      ExtM F FI (2 + k + 1) (p.1.push (mword p.1 p.2 W[2 + k]!),
        p.2.push (invM 5 133 (mword p.1 p.2 W[2 + k]!))) := by
    intro k hk p ⟨h1, h2', hj⟩
    obtain ⟨hl, hv⟩ := hW (2 + k) (by omega) hk
    have ew : mword p.1 p.2 W[2 + k]! = F (2 + k) := by
      rw [← hv]
      refine mword_congr (j := 2 + k) (fun i hi => ?_) (fun i hi => ?_) _ hl
      · rw [(hj i hi).1, ofFn_getElem! (by omega)]
      · rw [(hj i hi).2, ofFn_getElem! (F := FI) (by omega)]
    rw [ew]
    refine ⟨by simp [h1], by simp [h2'], fun i hi => ?_⟩
    rcases Nat.lt_or_ge i (2 + k) with h | h
    · rw [getElem!_pos _ i (by simp [h1]; omega), Array.getElem_push_lt (by omega),
        ← getElem!_pos _ i (by omega), getElem!_pos (p.2.push _) i (by simp [h2']; omega),
        Array.getElem_push_lt (by omega), ← getElem!_pos _ i (by omega)]
      exact hj i h
    · have e : i = 2 + k := by omega
      subst e
      rw [getElem!_pos _ (2 + k) (by simp [h1]), getElem!_pos (p.2.push _) (2 + k)
        (by simp [h2'])]
      have e1 : (p.1.push (F (2 + k)))[2 + k]'(by simp [h1]) = F (2 + k) := by
        simp only [← h1, Array.getElem_push_eq]
      have e2 : (p.2.push (invM 5 133 (F (2 + k))))[2 + k]'(by simp [h2']) = FI (2 + k) := by
        simp only [← h2', Array.getElem_push_eq]
        rw [h2']
        exact hinv _ hk
      exact ⟨e1, e2⟩
  have hloop : ∀ k, 2 + k ≤ s → ExtM F FI (2 + k)
      ((List.range' 2 k).foldl (fun (p : Array (Array (Array Nat)) × Array (Array (Array Nat))) j =>
        (p.1.push (mword p.1 p.2 W[j]!), p.2.push (invM 5 133 (mword p.1 p.2 W[j]!))))
        (orig, orig.map (invM 5 133))) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hm, by simp [hm], fun j hj => ⟨hO j hj, ?_⟩⟩
      simp only [List.range'_zero, List.foldl_nil]
      rw [getElem!_pos _ j (by simp [hm]; exact hj), Array.getElem_map, ← getElem!_pos orig j
        (by omega), hO j hj]
      exact hinv j (by omega)
    | succ k ih =>
      intro hk
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact step k (by omega) _ (ih (by omega))
  obtain ⟨hS, hSi, hj⟩ := hloop (s - 2) (by omega)
  have e : extendStrongM orig W = (List.range' 2 (s - 2)).foldl
      (fun (p : Array (Array (Array Nat)) × Array (Array (Array Nat))) j =>
        (p.1.push (mword p.1 p.2 W[j]!), p.2.push (invM 5 133 (mword p.1 p.2 W[j]!))))
      (orig, orig.map (invM 5 133)) := by
    unfold extendStrongM
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl, hm, hs]
  rw [e]
  have hs' : 2 + (s - 2) = s := by omega
  rw [hs'] at hS hSi hj
  refine Prod.ext (Array.ext (by simp [hS]) fun i h1 h2 => ?_) (Array.ext (by simp [hSi])
    fun i h1 h2 => ?_)
  · have hi : i < s := by simpa using h2
    rw [← getElem!_pos _ i h1, (hj i hi).1, Array.getElem_ofFn]
  · have hi : i < s := by simpa using h2
    rw [← getElem!_pos _ i h1, (hj i hi).2, Array.getElem_ofFn]

end CFSG.KS.SporSch

end
