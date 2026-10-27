
module

public import CFSG.Sporadic.Co1Block.TwoBExtraCheckInputs

public section

namespace CFSG.KC.Co1B

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native

theorem nat_all_of {n : Nat} {f : (i : Nat) → i < n → Bool} (h : ∀ i (hi : i < n), f i hi = true) :
    Nat.all n f = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true]
    exact ⟨ih fun i hi => h i (by omega), h n (by omega)⟩

@[expose] def TabInv (T : List (Nat × Nat)) (tab : Array Nat) : Prop :=
  tab.size = 2 ^ 24 ∧ ∀ x (hx : x < tab.size),
    1365 ≤ tab[x] ∨ ∃ hk : tab[x] < T.length, inTriN T[tab[x]] x = true

theorem tabInv_set {T : List (Nat × Nat)} {tab : Array Nat} (h : TabInv T tab) {i k : Nat}
    (hk : k < T.length) (hi : inTriN T[k] i = true) : TabInv T (tab.setIfInBounds i k) := by
  refine ⟨by rw [Array.size_setIfInBounds]; exact h.1, fun x hx => ?_⟩
  have hx' : x < tab.size := by rwa [Array.size_setIfInBounds] at hx
  rw [Array.getElem_setIfInBounds hx']
  by_cases hix : i = x
  · subst hix
    simp only [↓reduceIte]
    exact Or.inr ⟨hk, hi⟩
  · simp only [hix, ↓reduceIte]
    exact h.2 x hx'

theorem tabInv_foldl (T : List (Nat × Nat)) : ∀ (L : List ((Nat × Nat) × Nat)) (tab : Array Nat),
    (∀ q ∈ L, ∃ hq : q.2 < T.length, T[q.2] = q.1) → TabInv T tab →
    TabInv T (L.foldl (fun tab p =>
      ((tab.set! p.1.1 p.2).set! p.1.2 p.2).set! (p.1.1 ^^^ p.1.2) p.2) tab)
  | [], _, _, h => h
  | q :: L, tab, hL, h => by
    rw [List.foldl_cons]
    refine tabInv_foldl T L _ (fun r hr => hL r (List.mem_cons_of_mem _ hr)) ?_
    obtain ⟨hq, he⟩ := hL q List.mem_cons_self
    simp only [Array.set!_eq_setIfInBounds]
    refine tabInv_set (tabInv_set (tabInv_set h hq ?_) hq ?_) hq ?_ <;>
      simp [inTriN, he]

theorem tabInv_triTable (T : List (Nat × Nat)) : TabInv T (triTable T) := by
  have h0 : TabInv T (Array.replicate (2 ^ 24) 1365) :=
    ⟨Array.size_replicate, fun x hx => Or.inl (by simp)⟩
  have hL : ∀ q ∈ T.zipIdx, ∃ hq : q.2 < T.length, T[q.2] = q.1 := by
    intro q hq
    have h := List.mem_zipIdx_iff_getElem?.1 hq
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 h
    exact ⟨hlt, he⟩
  have := tabInv_foldl T T.zipIdx _ hL h0
  simpa [triTable] using this

theorem tabSoundOf_triTable (T : List (Nat × Nat)) : tabSoundOf (triTable T) T.toArray = true := by
  obtain ⟨hs, hinv⟩ := tabInv_triTable T
  unfold tabSoundOf CFSG.Monster.B.Co2.Native.allLt
  refine nat_all_of fun x hx => ?_
  have hx' : x < (triTable T).size := by rw [hs]; exact hx
  change (decide (1365 ≤ (triTable T)[x]!) || inTriN T.toArray[(triTable T)[x]!]! x) = true
  rw [getElem!_pos (triTable T) x hx']
  rcases hinv x hx' with h | ⟨hk, h⟩
  · simp [h]
  · have hk' : (triTable T)[x] < T.toArray.size := by rw [List.size_toArray]; exact hk
    rw [getElem!_pos T.toArray _ hk']
    simp [h]

end CFSG.KC.Co1B

end
