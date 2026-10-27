module

public import Certificates.Data.Kernel.BabyMonster.PktShape
public import CFSG.Certificates.Kernel.BabyMonster.PktDecode

public section

namespace CFSG.KC.BM.Pkt

open CFSG.KC.BM CFSG.KC.YModel CFSG.KC.BM.Dy
open CFSG.Monster.B.Native (packetRowShapeOK numOfCode)

@[expose] def rowP (r : Array (Nat × Int)) : Prop :=
  ∀ t < r.size, (r[t]!).1 < 4371 ∧ (t = 0 ∨ (r[t - 1]!).1 < (r[t]!).1)

@[expose] def lastP (r : Array (Nat × Int)) : Nat := if r.size = 0 then 0 else (r[r.size - 1]!).1 + 1

theorem rowP_empty : rowP #[] := fun t ht => absurd ht (Nat.not_lt_zero t)

theorem rowP_push {r : Array (Nat × Int)} {x : Nat × Int} (hr : rowP r) (h1 : x.1 < 4371)
    (h2 : lastP r ≤ x.1) : rowP (r.push x) := by
  intro t ht
  rw [Array.size_push] at ht
  rw [getElem!_push r x t, getElem!_push r x (t - 1)]
  rcases Nat.lt_or_ge t r.size with h | h
  · have h' : t - 1 < r.size := by omega
    rw [if_pos h, if_pos h']
    exact hr t h
  · have e : t = r.size := by omega
    subst e
    rw [if_neg (Nat.lt_irrefl _), if_pos rfl]
    refine ⟨h1, ?_⟩
    rcases Nat.eq_zero_or_pos r.size with h0 | h0
    · exact Or.inl h0
    · have h' : r.size - 1 < r.size := by omega
      rw [if_pos h']
      unfold lastP at h2
      rw [if_neg (Nat.pos_iff_ne_zero.1 h0)] at h2
      exact Or.inr h2

theorem lastP_push (r : Array (Nat × Int)) (x : Nat × Int) : lastP (r.push x) = x.1 + 1 := by
  unfold lastP
  rw [Array.size_push, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel, getElem!_push,
    if_neg (Nat.lt_irrefl _), if_pos rfl]

theorem rowShape_of {r : Array (Nat × Int)} (hr : rowP r) (hn : r.size ≠ 0) :
    packetRowShapeOK r = true := by
  unfold packetRowShapeOK
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨decide_eq_true (Nat.pos_iff_ne_zero.2 hn), fun t ht => ?_⟩
  obtain ⟨a, b⟩ := hr t (List.mem_range.1 ht)
  rw [Bool.and_eq_true, decide_eq_true a, Bool.or_eq_true, beq_iff_eq]
  refine ⟨rfl, ?_⟩
  rcases b with b | b
  · exact Or.inl b
  · exact Or.inr (decide_eq_true b)

@[expose] noncomputable def shOk (st : Nat × Nat × Bool) (v : Nat) : Bool :=
  andB st.2.2 (andB (Nat.blt (v % 8192) 4371) (Nat.ble st.2.1 (v % 8192)))

theorem shStep_eq (st : Nat × Nat × Bool) (v : Nat) :
    shStep st v = Bool.rec (motive := fun _ => Nat × Nat × Bool) (st.1, v % 8192 + 1, shOk st v)
      (st.1 + 1, 0, shOk st v) (Nat.beq (v / 65536) 1) := rfl

theorem shStep_end {st : Nat × Nat × Bool} {v : Nat} (h : v / 65536 = 1) :
    shStep st v = (st.1 + 1, 0, shOk st v) := by
  have hb : Nat.beq (v / 65536) 1 = true := by
    rw [h]
    rfl
  have e := shStep_eq st v
  rw [hb] at e
  exact e

theorem shStep_mid {st : Nat × Nat × Bool} {v : Nat} (h : v / 65536 ≠ 1) :
    shStep st v = (st.1, v % 8192 + 1, shOk st v) := by
  have hb : Nat.beq (v / 65536) 1 = false := by
    cases e : Nat.beq (v / 65536) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h
  have e := shStep_eq st v
  rw [hb] at e
  exact e

theorem shOk_facts {st : Nat × Nat × Bool} {v : Nat} (h : shOk st v = true) :
    st.2.2 = true ∧ v % 8192 < 4371 ∧ st.2.1 ≤ v % 8192 := by
  obtain ⟨h0, h⟩ := andB_true h
  obtain ⟨h1, h2⟩ := andB_true h
  exact ⟨h0, Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2⟩

@[expose] def ShInv (rr : Array (Array (Nat × Int)) × Array (Nat × Int)) (st : Nat × Nat × Bool) :
    Prop :=
  st.2.2 = true → st.1 = rr.1.size ∧ (∀ g ∈ rr.1.toList, packetRowShapeOK g = true) ∧
    rowP rr.2 ∧ st.2.1 = lastP rr.2

theorem shInv_step {rr : Array (Array (Nat × Int)) × Array (Nat × Int)} {st : Nat × Nat × Bool}
    (h : ShInv rr st) (v : Nat) : ShInv (entStep rr v) (shStep st v) := by
  unfold ShInv at h ⊢
  intro hok
  by_cases hv : v / 65536 = 1
  · rw [shStep_end hv] at hok ⊢
    obtain ⟨h0, h1, h2⟩ := shOk_facts hok
    obtain ⟨e1, eR, er, ep⟩ := h h0
    have ex : entStep rr v =
        (rr.1.push (rr.2.push (v % 8192, numOfCode (v / 8192 % 8))), #[]) := by
      unfold entStep
      rw [if_pos hv]
    rw [ex]
    have hp := rowP_push (x := (v % 8192, numOfCode (v / 8192 % 8))) er h1 (ep ▸ h2)
    refine ⟨by rw [e1, Array.size_push], ?_, rowP_empty, rfl⟩
    intro g hg
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact eR g hg
    · rw [hg]
      exact rowShape_of hp (by rw [Array.size_push]; exact Nat.succ_ne_zero _)
  · rw [shStep_mid hv] at hok ⊢
    obtain ⟨h0, h1, h2⟩ := shOk_facts hok
    obtain ⟨e1, eR, er, ep⟩ := h h0
    have ex : entStep rr v = (rr.1, rr.2.push (v % 8192, numOfCode (v / 8192 % 8))) := by
      unfold entStep
      rw [if_neg hv]
    rw [ex]
    exact ⟨e1, eR, rowP_push er h1 (ep ▸ h2),
      (lastP_push rr.2 (v % 8192, numOfCode (v / 8192 % 8))).symm⟩

theorem shInv_foldl : ∀ (vs : List Nat) (rr : Array (Array (Nat × Int)) × Array (Nat × Int))
    (st : Nat × Nat × Bool), ShInv rr st → ShInv (vs.foldl entStep rr) (vs.foldl shStep st)
  | [], _, _, h => h
  | v :: vs, _, _, h => shInv_foldl vs _ _ (shInv_step h v)

theorem shRec_foldl (N : Nat) : ∀ n : Nat,
    Nat.rec (motive := fun _ => Nat × Nat × Bool) (0, 0, true) (fun i ih => shStep ih (entV N i)) n =
      ((List.range n).map (entV N)).foldl shStep (0, 0, true)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append, ← shRec_foldl N n]
    rfl

theorem shape_rows {p : Nat × Nat} (h : shapeOK p = true) :
    (lineRows p).size = 4371 ∧ ∀ g ∈ (lineRows p).toList, packetRowShapeOK g = true := by
  have e : shapeOK p = andB (Nat.beq (Nat.rec (motive := fun _ => Nat × Nat × Bool) (0, 0, true)
      (fun i ih => shStep ih (entV p.1 i)) (p.2 / 3)).1 4371)
      (Nat.rec (motive := fun _ => Nat × Nat × Bool) (0, 0, true)
        (fun i ih => shStep ih (entV p.1 i)) (p.2 / 3)).2.2 := rfl
  rw [e, shRec_foldl] at h
  obtain ⟨h1, h2⟩ := andB_true h
  have hI : ShInv (#[], #[]) (0, 0, true) := fun _ => ⟨rfl, fun g hg => absurd hg (by simp),
    rowP_empty, rfl⟩
  obtain ⟨e1, eR, -, -⟩ := shInv_foldl ((List.range (p.2 / 3)).map (entV p.1)) _ _ hI h2
  refine ⟨?_, eR⟩
  unfold lineRows
  rw [← e1]
  exact Nat.eq_of_beq_eq_true h1

theorem foldl_size_add {α : Type} : ∀ (L : List (Array α)) (n : Nat),
    L.foldl (fun n r => n + r.size) n = n + L.foldl (fun n r => n + r.size) 0
  | [], n => rfl
  | r :: L, n => by
    rw [List.foldl_cons, List.foldl_cons, foldl_size_add L (n + r.size),
      foldl_size_add L (0 + r.size)]
    omega

theorem entStep_count : ∀ (vs : List Nat) (rr : Array (Array (Nat × Int)) × Array (Nat × Int)),
    (vs.foldl entStep rr).1.toList.foldl (fun n r => n + r.size) 0 + (vs.foldl entStep rr).2.size =
      rr.1.toList.foldl (fun n r => n + r.size) 0 + rr.2.size + vs.length
  | [], _ => rfl
  | v :: vs, rr => by
    rw [List.foldl_cons, entStep_count vs, List.length_cons]
    unfold entStep
    by_cases hv : v / 65536 = 1
    · rw [if_pos hv]
      simp only [Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Array.size_push, List.size_toArray, List.length_nil]
      omega
    · rw [if_neg hv]
      simp only [Array.size_push]
      omega

theorem rowsCount_lineRows {p : Nat × Nat} (h : lineOK p = true) :
    (lineRows p).toList.foldl (fun n r => n + r.size) 0 = p.2 / 3 := by
  obtain ⟨h1, -, -, h4, -⟩ := lineOK_facts h
  have hr : (((List.range (p.2 / 3)).map (entV p.1)).foldl entStep (#[], #[])).2 = #[] := by
    have e : List.range (p.2 / 3) = List.range (p.2 / 3 - 1) ++ [p.2 / 3 - 1] := by
      rw [← List.range_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel h1]
    rw [e, List.map_append, List.map_cons, List.map_nil]
    exact entStep_last h4 _
  have c := entStep_count ((List.range (p.2 / 3)).map (entV p.1)) (#[], #[])
  rw [hr, List.length_map, List.length_range] at c
  unfold lineRows
  simpa using c

theorem natRec_foldl (h : Nat → Nat) : ∀ n : Nat,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => Nat.add ih (h i)) n =
      (List.range n).foldl (fun s i => s + h i) 0
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, ← natRec_foldl h n]
    rfl

theorem countOK_sound {CH : List (Nat × Nat)} {S : List Nat} (h : countOK CH S = true) :
    (List.range 48).foldl (fun s i => s + (lineOf CH S i).2 / 3) 0 = 259183 := by
  rw [← natRec_foldl (fun i => (lineOf CH S i).2 / 3) 48]
  exact Nat.eq_of_beq_eq_true h

end CFSG.KC.BM.Pkt

end
