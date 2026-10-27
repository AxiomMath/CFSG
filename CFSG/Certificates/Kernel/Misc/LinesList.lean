module

public import CFSG.Certificates.Kernel.Misc.LinesIdx
public import CFSG.Certificates.Kernel.Misc.LinesNative
import CFSG.Certificates.Kernel.Common.QSort
public import Mathlib.Data.Finset.Sort

public section

namespace CFSG.KC.Misc.Lines

open CFSG.Fischer.Native CFSG.F4.Native CFSG.Sporadic.Th.Native

@[expose] def slA (LT : Array (Array Nat)) (x y : Nat) : Array Nat :=
  LT[x * 693 + y]!.qsort (· < ·)

@[expose] def goodB (P : Array Flags) (LT : Array (Array Nat)) (x y : Nat) : Bool :=
  P[x]![y]! && ((slA LT x y)[0]! == x && (slA LT x y)[1]! == y)

@[expose] def Prs (P : Array Flags) (LT : Array (Array Nat)) : List (Nat × Nat) :=
  (List.range 693).flatMap fun x =>
    ((List.range' (x + 1) (693 - (x + 1))).filter (goodB P LT x)).map fun y => (x, y)

theorem foldl_append_toArray {α β : Type} (l : List α) (F : α → List β) (init : Array β) :
    l.foldl (fun b a => b ++ (F a).toArray) init = init ++ (l.flatMap F).toArray := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons]
    simp [Array.append_assoc]

theorem legacyRange_size' (s e : Nat) : [s:e].size = e - s := by
  simp [Std.Legacy.Range.size]

theorem lineList_eq (P : Array Flags) (LT : Array (Array Nat)) :
    lineList P LT = ((Prs P LT).map fun p => slA LT p.1 p.2).toArray := by
  unfold lineList
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [forIn_cond_push, id_bind_eq, List.forIn_pure_yield_eq_foldl, legacyRange_size']
  rw [foldl_append_toArray]
  simp only [Array.empty_append, Nat.sub_zero, ← List.range_eq_range', Prs, slA,
    List.map_flatMap, List.map_map, Function.comp_def]
  rfl

theorem mem_Prs {P : Array Flags} {LT : Array (Array Nat)} {x y : Nat} :
    (x, y) ∈ Prs P LT ↔ x < 693 ∧ x < y ∧ y < 693 ∧ goodB P LT x y = true := by
  unfold Prs
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, List.mem_range'_1,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x', hx', y', ⟨⟨hy1, hy2⟩, hg⟩, rfl, rfl⟩
    exact ⟨hx', by omega, by omega, hg⟩
  · rintro ⟨hx, hxy, hy, hg⟩
    exact ⟨x, hx, y, ⟨⟨by omega, by omega⟩, hg⟩, rfl, rfl⟩

theorem Prs_nodup (P : Array Flags) (LT : Array (Array Nat)) : (Prs P LT).Nodup := by
  unfold Prs
  rw [List.nodup_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · refine List.Nodup.map (fun a b h => (Prod.mk.inj h).2) ?_
    exact (List.nodup_range' (n := 693 - (x + 1)) (s := x + 1)).filter _
  · refine (List.nodup_range (n := 693)).imp ?_
    intro a b hab p hpa hpb
    simp only [List.mem_map] at hpa hpb
    obtain ⟨y1, -, rfl⟩ := hpa
    obtain ⟨y2, -, h⟩ := hpb
    exact hab (Prod.mk.inj h).1.symm

theorem qsort_toList_eq (l : List Nat) (hnd : l.Nodup) :
    (l.toArray.qsort (· < ·)).toList = l.toFinset.sort (· ≤ ·) := by
  have htrans : ∀ a b c : Nat, decide (a < b) = true → decide (b < c) = true →
      decide (a < c) = true := by
    intro a b c h1 h2
    simp only [decide_eq_true_eq] at h1 h2 ⊢
    omega
  have hasymm : ∀ a b : Nat, decide (a < b) = true → decide (b < a) = false := by
    intro a b h1
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h1 ⊢
    omega
  have hperm : (l.toArray.qsort (· < ·)).toList.Perm l := by
    have := CFSG.KC.QSort.qsort_perm l.toArray (fun a b => decide (a < b))
    rw [Array.perm_iff_toList_perm] at this
    simpa using this
  have hsorted : (l.toArray.qsort (· < ·)).toList.Pairwise (fun a b => a ≤ b) := by
    have := CFSG.KC.QSort.qsort_pairwise l.toArray (fun a b => decide (a < b)) htrans hasymm
    refine this.imp ?_
    intro a b h
    simp only [decide_eq_false_iff_not] at h
    omega
  have hlt : (l.toArray.qsort (· < ·)).toList.Pairwise (· < ·) := by
    have := hsorted.and (hperm.nodup_iff.2 hnd)
    exact this.imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)
  have hlt' : (l.toFinset.sort (· ≤ ·)).Pairwise (· < ·) := by
    have := (Finset.pairwise_sort l.toFinset (· ≤ ·)).and (Finset.sort_nodup l.toFinset (· ≤ ·))
    exact this.imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)
  apply List.Pairwise.eq_of_mem_iff hlt hlt'
  intro a
  rw [hperm.mem_iff, Finset.mem_sort, List.mem_toFinset]

structure LinesData (rb : Nat → Nat → Bool) (L : Array (Array Nat)) : Prop where
  mem : ∀ i < L.size, ∃ x < 693, ∃ y < 693, x ≠ y ∧ rb x y = true ∧
    (L[i]!).toList = (Ln rb x y).sort (· ≤ ·)
  inj : ∀ i < L.size, ∀ j < L.size, (L[i]!).toList = (L[j]!).toList → i = j
  surj : ∀ x < 693, ∀ y < 693, x ≠ y → rb x y = true →
    ∃ i < L.size, (L[i]!).toList = (Ln rb x y).sort (· ≤ ·)

variable {P : Array Flags} {pl : Array (Array Nat)} {LT : Array (Array Nat)}
  {rb : Nat → Nat → Bool} {PL : Nat → List Nat} {lf : Nat → Nat → List Nat}

theorem slA_toList (T : Tabs P pl LT rb PL lf) (G : Geom rb PL lf) {x y : Nat} (hx : x < 693)
    (hy : y < 693) (hxy : x < y) (hr : rb x y = true) :
    (slA LT x y).toList = (Ln rb x y).sort (· ≤ ·) := by
  have hLT := T.LT_get x hx y hy
  rw [if_pos hr] at hLT
  unfold slA
  have e : (lf x y).toFinset = Ln rb x y := by
    ext z
    rw [List.mem_toFinset, G.lmem x hx y hy (Nat.ne_of_lt hxy) hr z]
  rw [hLT, qsort_toList_eq _ (G.lnodup x hx y hy hxy hr), e]

theorem good_pair (T : Tabs P pl LT rb PL lf) {p : Nat × Nat} (h : p ∈ Prs P LT) :
    p.1 < 693 ∧ p.1 < p.2 ∧ p.2 < 693 ∧ rb p.1 p.2 = true ∧
      (slA LT p.1 p.2)[0]! = p.1 ∧ (slA LT p.1 p.2)[1]! = p.2 := by
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hxy, hy, hg⟩ := mem_Prs.1 h
  unfold goodB at hg
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨h1, h2, h3⟩ := hg
  exact ⟨hx, hxy, hy, by rw [← T.P_get x hx y hy]; exact h1, h2, h3⟩

theorem lineList_data (T : Tabs P pl LT rb PL lf) (G : Geom rb PL lf) :
    LinesData rb (lineList P LT) := by
  rw [lineList_eq]
  have hsize : ((((Prs P LT).map fun p => slA LT p.1 p.2)).toArray).size = (Prs P LT).length := by
    simp
  have hget : ∀ i (hi : i < (Prs P LT).length),
      ((((Prs P LT).map fun p => slA LT p.1 p.2)).toArray)[i]! =
        slA LT ((Prs P LT)[i]).1 ((Prs P LT)[i]).2 := by
    intro i hi
    simp [hi]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hsize] at hi
    rw [hget i hi]
    have hp : (Prs P LT)[i] ∈ Prs P LT := List.getElem_mem hi
    obtain ⟨hx, hxy, hy, hr, -, -⟩ := good_pair T hp
    exact ⟨_, hx, _, hy, Nat.ne_of_lt hxy, hr, slA_toList T G hx hy hxy hr⟩
  · intro i hi j hj h
    rw [hsize] at hi hj
    rw [hget i hi, hget j hj] at h
    have hpi : (Prs P LT)[i] ∈ Prs P LT := List.getElem_mem hi
    have hpj : (Prs P LT)[j] ∈ Prs P LT := List.getElem_mem hj
    obtain ⟨-, -, -, -, hi0, hi1⟩ := good_pair T hpi
    obtain ⟨-, -, -, -, hj0, hj1⟩ := good_pair T hpj
    have harr : slA LT ((Prs P LT)[i]).1 ((Prs P LT)[i]).2 =
        slA LT ((Prs P LT)[j]).1 ((Prs P LT)[j]).2 := Array.toList_inj.1 h
    have e1 : ((Prs P LT)[i]).1 = ((Prs P LT)[j]).1 := by rw [← hi0, ← hj0, harr]
    have e2 : ((Prs P LT)[i]).2 = ((Prs P LT)[j]).2 := by rw [← hi1, ← hj1, harr]
    exact (List.Nodup.getElem_inj_iff (Prs_nodup P LT)).1 (Prod.ext e1 e2)
  · intro x hx y hy hne hr
    have hcard : (Ln rb x y).card = 5 := G.rel.card5' hx hy hne hr
    have hlen : ((Ln rb x y).sort (· ≤ ·)).length = 5 := by rw [Finset.length_sort, hcard]
    have hsorted : ((Ln rb x y).sort (· ≤ ·)).Pairwise (· < ·) :=
      (Finset.sortedLT_sort (Ln rb x y)).pairwise
    have h0 : 0 < ((Ln rb x y).sort (· ≤ ·)).length := by omega
    have h1 : 1 < ((Ln rb x y).sort (· ≤ ·)).length := by omega
    have hx'S : ((Ln rb x y).sort (· ≤ ·))[0] ∈ Ln rb x y :=
      (Finset.mem_sort (· ≤ ·)).1 (List.getElem_mem h0)
    have hy'S : ((Ln rb x y).sort (· ≤ ·))[1] ∈ Ln rb x y :=
      (Finset.mem_sort (· ≤ ·)).1 (List.getElem_mem h1)
    have hlt : ((Ln rb x y).sort (· ≤ ·))[0] < ((Ln rb x y).sort (· ≤ ·))[1] :=
      List.pairwise_iff_getElem.1 hsorted 0 1 h0 h1 (by omega)
    generalize hx' : ((Ln rb x y).sort (· ≤ ·))[0] = x' at hx'S hlt
    generalize hy' : ((Ln rb x y).sort (· ≤ ·))[1] = y' at hy'S hlt
    have hx'693 := lt_of_mem_Ln hx'S
    have hy'693 := lt_of_mem_Ln hy'S
    have hr' : rb x' y' = true := G.rel.perp_of_mem hx hy hr hx'S hy'S
    have hLn : Ln rb x' y' = Ln rb x y := G.rel.Ln_eq hx hy hne hr (Nat.ne_of_lt hlt) hx'S hy'S
    have hlist := slA_toList T G hx'693 hy'693 hlt hr'
    rw [hLn] at hlist
    have e0 : (slA LT x' y')[0]! = x' := by
      rw [← Array.getElem!_toList, hlist, getElem!_pos ((Ln rb x y).sort (· ≤ ·)) 0 h0, hx']
    have e1 : (slA LT x' y')[1]! = y' := by
      rw [← Array.getElem!_toList, hlist, getElem!_pos ((Ln rb x y).sort (· ≤ ·)) 1 h1, hy']
    have hgoodB : goodB P LT x' y' = true := by
      unfold goodB
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨by rw [T.P_get x' hx'693 y' hy'693]; exact hr', e0, e1⟩
    have hmem : (x', y') ∈ Prs P LT := mem_Prs.2 ⟨hx'693, hlt, hy'693, hgoodB⟩
    obtain ⟨i, hi, hiEq⟩ := List.mem_iff_getElem.1 hmem
    refine ⟨i, by rw [hsize]; exact hi, ?_⟩
    rw [hget i hi, hiEq]
    exact hlist

end CFSG.KC.Misc.Lines

end
