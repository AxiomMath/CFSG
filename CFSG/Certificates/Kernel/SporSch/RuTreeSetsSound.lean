module

public import CFSG.Sporadic.Schreier.RuCheckTreeInputs

public section

namespace CFSG.KS.RuTree

open CFSG.Sporadic.RuSchreier CFSG.Certificates.Native

theorem push_get!_lt {A : Array (List Nat)} {x : List Nat} {i : Nat} (h : i < A.size) :
    (A.push x)[i]! = A[i]! := by
  have hne : i ≠ A.size := by omega
  simp only [getElem!_def, Array.getElem?_push, hne, ↓reduceIte]

theorem push_get!_last {A : Array (List Nat)} {x : List Nat} : (A.push x)[A.size]! = x := by
  simp only [getElem!_def, Array.getElem?_push, ↓reduceIte]

theorem foldPush_spec (g : Nat → List Nat → List Nat) (p : Nat → Nat) (init : List Nat) :
    ∀ n, ((List.range' 1 n).foldl (fun s j => s.push (g j s[p j]!)) #[init]).size = n + 1 ∧
      ((List.range' 1 n).foldl (fun s j => s.push (g j s[p j]!)) #[init])[0]! = init ∧
      ∀ j, 1 ≤ j → j ≤ n → p j < j →
        ((List.range' 1 n).foldl (fun s j => s.push (g j s[p j]!)) #[init])[j]! =
          g j ((List.range' 1 n).foldl (fun s j => s.push (g j s[p j]!)) #[init])[p j]! := by
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl, fun j h1 h2 _ => absurd h2 (by omega)⟩
  | succ n ih =>
    obtain ⟨hs, h0, hj⟩ := ih
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 1 n).foldl (fun s j => s.push (g j s[p j]!)) #[init] = A at hs h0 hj
    refine ⟨by rw [Array.size_push, hs], by rw [push_get!_lt (by omega), h0], fun j h1 h2 h3 => ?_⟩
    rw [push_get!_lt (i := p j) (by omega)]
    rcases Nat.lt_or_ge j (n + 1) with hl | hl
    · rw [push_get!_lt (by omega), hj j h1 (by omega) h3]
    · have e : j = A.size := by omega
      have e' : 1 + 1 * n = j := by omega
      rw [e', e, push_get!_last, ← e]

theorem ruTreeSets_spec : ruTreeSets.size = 593775 ∧ ruTreeSets[0]! = ruFixZ ∧
    ∀ j, 1 ≤ j → j < 593775 → ruTreePar[j]! < j →
      ruTreeSets[j]! = imgSorted ruTreeGens[ruTreeLab[j]!]! ruTreeSets[ruTreePar[j]!]! := by
  have e : ruTreeSets = (List.range' 1 593774).foldl
      (fun s j => s.push (imgSorted ruTreeGens[ruTreeLab[j]!]! s[ruTreePar[j]!]!)) #[ruFixZ] := by
    unfold ruTreeSets
    simp only [Array.mkEmpty_eq, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
    rfl
  obtain ⟨h1, h2, h3⟩ := foldPush_spec (fun j L => imgSorted ruTreeGens[ruTreeLab[j]!]! L)
    (fun j => ruTreePar[j]!) ruFixZ 593774
  rw [e]
  exact ⟨h1, h2, fun j a b c => h3 j a (by omega) c⟩

theorem sorted_strict {S : Array (List Nat)}
    (h : ∀ i j, i < S.size → j < S.size → S[i]! = S[j]! → i = j) : ruSortedStrict S = true := by
  unfold ruSortedStrict
  rw [decide_eq_true_iff]
  have hnd : S.toList.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro a b e
    have := h a b (by simp) (by simp)
      (by simpa [getElem!_def, Array.getElem?_eq_getElem, a.2, b.2] using e)
    exact Fin.ext this
  have hp := List.pairwise_mergeSort (l := S.toList) (le := fun x y : List Nat => decide (x ≤ y))
    (fun a b c hab hbc => by
      rw [decide_eq_true_iff] at hab hbc ⊢
      exact le_trans hab hbc)
    (fun a b => by
      rcases le_total a b with h | h
      · simp [h]
      · simp [h])
  have hnd' := (List.mergeSort_perm S.toList fun x y => decide (x ≤ y)).nodup_iff.2 hnd
  have hlt : (S.toList.mergeSort fun x y => decide (x ≤ y)).Pairwise (· < ·) := by
    refine (hp.and hnd').imp ?_
    intro a b ⟨hab, hne⟩
    rw [decide_eq_true_iff] at hab
    exact lt_of_le_of_ne hab hne
  exact hlt.isChain

end CFSG.KS.RuTree

end
