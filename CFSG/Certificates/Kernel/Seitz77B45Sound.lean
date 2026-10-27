module

public import Certificates.Data.Kernel.Seitz77B45K
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.KC.SeitzB45

open Certificates.Seitz77CaseB45 CFSG.PSL3Four.Native

theorem foldl_push_toList {β : Type} (f : ℕ → β) (l : List ℕ) (r : Array β) :
    (l.foldl (fun b a => b.push (f a)) r).toList = r.toList ++ l.map f := by
  induction l generalizing r with
  | nil => simp
  | cons a l ih => simp [ih]

theorem mtArr_toList : mtArr.toList = (List.range 256).flatMap fun i =>
    (List.range 256).map fun j => posOf idxTL etl.tabs (comp 42 etl.tabs[i]! etl.tabs[j]!) := by
  unfold mtArr
  simp only [Id.run, bind_pure_comp, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, map_pure, pure_bind]
  have key : ∀ (l : List ℕ) (r : Array ℕ), (l.foldl (fun r i => (List.range' 0 256).foldl
      (fun b a => b.push (posOf idxTL etl.tabs (comp 42 etl.tabs[i]! etl.tabs[a]!))) r) r).toList =
      r.toList ++ l.flatMap fun i => (List.range 256).map fun j =>
        posOf idxTL etl.tabs (comp 42 etl.tabs[i]! etl.tabs[j]!) := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro r
      rw [List.foldl_cons, ih, foldl_push_toList (fun a => posOf idxTL etl.tabs
        (comp 42 etl.tabs[i]! etl.tabs[a]!)), List.flatMap_cons, List.range_eq_range']
      simp
  change (List.foldl _ (Array.mkEmpty 65536) (List.range' 0 256)).toList = _
  rw [key, List.range_eq_range']
  simp

theorem len_flatMap (f : ℕ → ℕ → ℕ) : ∀ n : ℕ,
    ((List.range n).flatMap fun i => (List.range 256).map (f i)).length = n * 256
  | 0 => rfl
  | n + 1 => by
    rw [show List.range (n + 1) = List.range n ++ [n] from List.range_succ, List.flatMap_append,
      List.length_append, len_flatMap f n, List.flatMap_singleton, List.length_map,
      List.length_range]
    omega

theorem flatMap_get {f : ℕ → ℕ → ℕ} : ∀ (n : ℕ) {i j : ℕ}, i < n → j < 256 →
    ((List.range n).flatMap fun i => (List.range 256).map (f i))[i * 256 + j]! = f i j
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, j, hi, hj => by
    rw [show List.range (n + 1) = List.range n ++ [n] from List.range_succ, List.flatMap_append,
      List.flatMap_singleton]
    have hlen := len_flatMap f n
    rcases Nat.lt_or_ge i n with h | h
    · have hk : i * 256 + j < n * 256 := by nlinarith
      rw [getElem!_pos _ _ (by simp [hlen]; nlinarith), List.getElem_append_left (by rw [hlen]; exact hk),
        ← getElem!_pos _ _ (by rw [hlen]; exact hk)]
      exact flatMap_get n h hj
    · obtain rfl : i = n := by omega
      rw [getElem!_pos _ _ (by simp [hlen]; omega), List.getElem_append_right (by rw [hlen]; omega)]
      simp [hlen]

theorem mtArr_get : mtArr.size = 65536 ∧ ∀ i j, i < 256 → j < 256 →
    mtArr[i * 256 + j]! = posOf idxTL etl.tabs (comp 42 etl.tabs[i]! etl.tabs[j]!) := by
  have hl : mtArr.toList.length = 65536 := by
    rw [mtArr_toList, len_flatMap]
  refine ⟨by simpa using hl, fun i j hi hj => ?_⟩
  have hk : i * 256 + j < 65536 := by omega
  rw [getElem!_pos mtArr _ (by rw [← Array.length_toList, hl]; exact hk), ← Array.getElem_toList]
  have e := flatMap_get (f := fun i j => posOf idxTL etl.tabs (comp 42 etl.tabs[i]! etl.tabs[j]!))
    256 hi hj
  rw [getElem!_pos _ _ (by rw [len_flatMap]; omega)] at e
  simp only [mtArr_toList]
  exact e

theorem fb6_of {mt : Nat → Nat → Nat} {lab : Nat → Nat} {ladd : Nat → Nat → Nat}
    {MS : List Nat} {ST SL : List (List Nat)} (hMS : MS.length = 15)
    (hadm : ∀ c < 16, admOK ladd MS (4096 * c) 4096 = true)
    (hst : ∀ i < 15, statsF mt lab (MS.getD i 0) ((ST.getD i []).getD 0 0)
      [(ST.getD i []).getD 1 0, (ST.getD i []).getD 2 0, (ST.getD i []).getD 3 0,
        (ST.getD i []).getD 4 0] ((ST.getD i []).getD 5 0) = true)
    (hcov : coverOKF mt 15 SL = true)
    (hsl : ∀ c < SL.length, sliceF mt lab (MS.getD ((SL.getD c []).getD 0 0) 0)
      ((ST.getD ((SL.getD c []).getD 0 0) []).getD 0 0)
      [(ST.getD ((SL.getD c []).getD 0 0) []).getD 1 0, (ST.getD ((SL.getD c []).getD 0 0) []).getD 2 0,
        (ST.getD ((SL.getD c []).getD 0 0) []).getD 3 0,
        (ST.getD ((SL.getD c []).getD 0 0) []).getD 4 0]
      ((ST.getD ((SL.getD c []).getD 0 0) []).getD 5 0)
      ((SL.getD c []).getD 1 0) ((SL.getD c []).getD 2 0) ((SL.getD c []).getD 3 0)
      ((SL.getD c []).getD 4 0) = true) :
    fb6Check mt lab ladd = true := by
  unfold fb6Check
  rw [List.all_eq_true]
  intro m hm
  have hm' := List.mem_range.1 hm
  by_cases hin : m ∈ MS
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hin
    have hgi : MS.getD i 0 = MS[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hMS] at hi
    have hs := hst i hi
    unfold statsF at hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    rw [hgi] at h1 h2 h3
    rw [Bool.or_eq_true]
    right
    unfold mainOK mainAux
    rw [h1, h2, h3, List.all_eq_true]
    intro a ha
    rw [List.all_eq_true]
    intro b hb
    have hc := hcov
    unfold coverOKF at hc
    simp only [List.all_eq_true, List.mem_range] at hc
    obtain ⟨s, hsm, hcs⟩ := List.any_eq_true.1 (hc i hi a ha b hb)
    obtain ⟨c, hcl, rfl⟩ := List.getElem_of_mem hsm
    have hgc : SL.getD c [] = SL[c] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl, Option.getD_some]
    unfold coversF at hcs
    simp only [Bool.and_eq_true, beq_iff_eq] at hcs
    obtain ⟨⟨h0, hra⟩, hrb⟩ := hcs
    have hk := hsl c hcl
    rw [hgc, h0, hgi] at hk
    unfold sliceF at hk
    rw [List.all_eq_true] at hk
    have hka := hk a ha
    rw [hra, Bool.not_true, Bool.false_or, List.all_eq_true] at hka
    have hkb := hka b hb
    rw [hrb, Bool.not_true, Bool.false_or] at hkb
    unfold condF at hkb
    exact hkb
  · have hc := hadm (m / 4096) (by omega)
    unfold admOK at hc
    rw [List.all_eq_true] at hc
    have hk := hc m (List.mem_range'.2 ⟨m % 4096, by omega, by omega⟩)
    rw [Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact absurd (List.contains_iff_mem.1 hk) hin
    · rw [hk, Bool.true_or]

end CFSG.KC.SeitzB45

end
