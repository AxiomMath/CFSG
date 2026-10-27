
module

public import CFSG.Certificates.Kernel.SporSch.HNF5ModSound
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
import CFSG.Certificates.Kernel.SporSch.HNF5Lane

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CFSG.ONSchreier.Native

theorem root5_sound {x : Nat} {cs : List Char} (h : dig5K x cs = true) :
    (Array.ofFn (n := 133) fun j => ((String.ofList cs).toList.getD j.val '0').toNat - '0'.toNat) =
      vec5 x := by
  obtain ⟨-, hd⟩ := F5Lane.dig5K_spec h
  unfold vec5
  rw [String.toList_ofList]
  exact congrArg Array.ofFn (funext fun j => hd j.val j.isLt)

theorem xstep5 {MT : Nat → Nat} {kA kB kV : Nat} {H : Array (Array (Array Nat))}
    {recs : List (Nat × Nat)}
    (hH0 : H[0]! = colsMat 133 (rows5 (slice5 MT kA)))
    (hH1 : H[1]! = colsMat 133 (rows5 (slice5 MT kB)))
    (hA : Canon5 (slice5 MT kA)) (hB : Canon5 (slice5 MT kB))
    (hX : ∀ i < 462, canon5 (slice5 MT kV i) = true)
    (hs : ∀ i, 1 ≤ i → i < 462 → (recs.getD i (0, 0)).1 < i ∧
      ((recs.getD i (0, 0)).2 = 1 ∨ (recs.getD i (0, 0)).2 = 2) ∧
      vm5 (slice5 MT (nIf(Nat.beq (recs.getD i (0, 0)).2 1, kA, kB)))
        (slice5 MT kV (recs.getD i (0, 0)).1) = slice5 MT kV i)
    {i : Nat} (h1 : 1 ≤ i) (h2 : i < 462) {acc : Array (Array Nat)}
    (hacc : ∀ t < i, acc[t]! = vec5 (slice5 MT kV t)) :
    mulVec 5 133 H[(recs.getD i (0, 0)).2 - 1]! acc[(recs.getD i (0, 0)).1]! =
      vec5 (slice5 MT kV i) := by
  obtain ⟨hlt, hl, he⟩ := hs i h1 h2
  rw [hacc _ hlt]
  rcases hl with hl | hl
  · rw [hl] at he ⊢
    change vm5 (slice5 MT kA) (slice5 MT kV (recs.getD i (0, 0)).1) = slice5 MT kV i at he
    rw [Nat.sub_self, hH0, mulVec5_sound hA (hX _ (by omega)), he]
  · rw [hl] at he ⊢
    change vm5 (slice5 MT kB) (slice5 MT kV (recs.getD i (0, 0)).1) = slice5 MT kV i at he
    have e : (2 : Nat) - 1 = 1 := rfl
    rw [e, hH1, mulVec5_sound hB (hX _ (by omega)), he]

theorem xvec5_sound {MT : Nat → Nat} {kA kB kV : Nat} {H : Array (Array (Array Nat))}
    {x0 : Array Nat} {recs : List (Nat × Nat)}
    (hH0 : H[0]! = colsMat 133 (rows5 (slice5 MT kA)))
    (hH1 : H[1]! = colsMat 133 (rows5 (slice5 MT kB)))
    (hA : Canon5 (slice5 MT kA)) (hB : Canon5 (slice5 MT kB))
    (hX : ∀ i < 462, canon5 (slice5 MT kV i) = true) (hlen : recs.length = 462)
    (h0 : vec5 (slice5 MT kV 0) = x0)
    (hs : ∀ i, 1 ≤ i → i < 462 → (recs.getD i (0, 0)).1 < i ∧
      ((recs.getD i (0, 0)).2 = 1 ∨ (recs.getD i (0, 0)).2 = 2) ∧
      vm5 (slice5 MT (nIf(Nat.beq (recs.getD i (0, 0)).2 1, kA, kB)))
        (slice5 MT kV (recs.getD i (0, 0)).1) = slice5 MT kV i) :
    (xVecs H x0 recs).size = 462 ∧
      (∀ i < 462, (xVecs H x0 recs)[i]! = vec5 (slice5 MT kV i)) ∧
      allBelowN 462 (fun i => i == 0 || (xVecs H x0 recs)[i]! ==
        mulVec 5 133 H[recs[i]!.2 - 1]! (xVecs H x0 recs)[recs[i]!.1]!) = true := by
  have push_lt : ∀ (acc : Array (Array Nat)) (v : Array Nat) {t : Nat}, t < acc.size →
      (acc.push v)[t]! = acc[t]! := fun acc v t ht => by
    rw [getElem!_pos (acc.push v) t (by rw [Array.size_push]; omega), getElem!_pos acc t ht,
      Array.getElem_push_lt]
  have push_eq : ∀ (acc : Array (Array Nat)) (v : Array Nat), (acc.push v)[acc.size]! = v :=
    fun acc v => by
      rw [getElem!_pos (acc.push v) acc.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]
  have inv : ∀ m, m ≤ 461 →
      (((recs.drop 1).take m).foldl (fun acc r => acc.push (mulVec 5 133 H[r.2 - 1]! acc[r.1]!))
        #[x0]).size = m + 1 ∧
      ∀ t < m + 1, (((recs.drop 1).take m).foldl
        (fun acc r => acc.push (mulVec 5 133 H[r.2 - 1]! acc[r.1]!)) #[x0])[t]! =
          vec5 (slice5 MT kV t) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨rfl, fun t ht => ?_⟩
      obtain rfl : t = 0 := by omega
      exact h0.symm
    | succ m ih =>
      intro hm
      obtain ⟨ihs, ihg⟩ := ih (by omega)
      have hr : (recs.drop 1)[m]? = some (recs.getD (m + 1) (0, 0)) := by
        rw [List.getElem?_drop, List.getD_eq_getElem?_getD, Nat.add_comm 1 m,
          List.getElem?_eq_getElem (by omega : m + 1 < recs.length), Option.getD_some]
      rw [List.take_add_one, hr, Option.toList_some, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      generalize ((recs.drop 1).take m).foldl
        (fun acc r => acc.push (mulVec 5 133 H[r.2 - 1]! acc[r.1]!)) #[x0] = acc at ihs ihg
      have hv := xstep5 hH0 hH1 hA hB hX hs (i := m + 1) (by omega) (by omega) ihg
      refine ⟨by rw [Array.size_push, ihs], fun t ht => ?_⟩
      rcases Nat.lt_or_ge t (m + 1) with htm | htm
      · rw [push_lt _ _ (by omega), ihg t htm]
      · obtain rfl : t = m + 1 := by omega
        rw [← ihs, push_eq, ihs, hv]
  have hL : (recs.drop 1).take 461 = recs.drop 1 :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  obtain ⟨hsz, hget⟩ := inv 461 le_rfl
  rw [hL] at hsz hget
  have hsz' : (xVecs H x0 recs).size = 462 := hsz
  have hget' : ∀ i < 462, (xVecs H x0 recs)[i]! = vec5 (slice5 MT kV i) := hget
  refine ⟨hsz', hget', ?_⟩
  unfold allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨i, hi⟩ -
  simp only
  by_cases i0 : i = 0
  · subst i0
    rfl
  · have hr : recs[i]! = recs.getD i (0, 0) := by
      rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rfl
    rw [hr, xstep5 hH0 hH1 hA hB hX hs (i := i) (by omega) hi (fun t ht => hget' t (by omega)),
      hget' i hi]
    simp

end CFSG.KS.SporSch

end
