module

public import CFSG.Certificates.Kernel.GilmanCensus.TailSound
public import Certificates.Data.Kernel.GilmanCensus.TailK

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

theorem distinctK_nodup : ∀ (l : List (List Int)), distinctK l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [distinctK, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, distinctK_nodup xs h.2⟩
    have := List.contains_iff_mem.mpr hx
    rw [h.1] at this
    exact Bool.false_ne_true this

theorem all_length {l : List (List Nat)} {n : Nat} (h : (l.all fun r => r.length == n) = true) :
    ∀ r ∈ l, r.length = n := by
  intro r hr
  rw [List.all_eq_true] at h
  exact beq_iff_eq.mp (h r hr)

theorem tailOk_tailS (mode n : Nat) (AR : Array IVec) (rho : Array Nat) (B : Array (Array Int))
    (R : Array IVec) (absidx F H : Array (Array Nat)) (d : Nat) (dk : DK)
    (hmode : mode = dk.mode) (hd : d = dk.d) (hR : LLI R = toI dk.R) (hAR : LLI AR = toI dk.AR)
    (habs : LL absidx = dk.absidx) (hrho : rho.toList = dk.rho) (hF : LL F = dk.F)
    (hH : LL H = dk.H) (h : tailOkK dk n (LLI B) = true) :
    ∃ dt, tailS mode n AR rho B true R absidx F H d = some dt ∧ Rel dt dk := by
  simp only [tailOkK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := h
  have hG : ∀ i j, i < dk.N → j < dk.N →
      gramK (LLI B) ((toI dk.R).getD i []) ((toI dk.R).getD j []) = gI dk i j := by
    intro i j hi hj
    unfold gramOkK at h14
    rw [List.all_eq_true] at h14
    have := h14 i (List.mem_range.mpr hi)
    rw [List.all_eq_true] at this
    exact beq_iff_eq.mp (this j (List.mem_range.mpr hj))
  have hl : ∀ i < dk.N, ∀ j < 128, (dk.reflP.getD i 0 >>> (7 * j)) % 128 =
      (((reflK (toI dk.R) (gI dk) n dk.N true).2.getD i []).getD j 0) := by
    intro i hi j hj
    unfold lanesOkK at h19
    rw [List.all_eq_true] at h19
    have := h19 i (List.mem_range.mpr hi)
    rw [List.all_eq_true] at this
    exact beq_iff_eq.mp (this j (List.mem_range.mpr hj))
  exact tailS_eq mode n AR rho B R absidx F H d dk hmode hd hR (distinctK_nodup _ h1)
    (all_length h2) h3 h4 hAR (distinctK_nodup _ h5) (all_length h6) h7 habs hrho hF
    (all_length h8) h9 hH (all_length h10) h11 h12 h13 hG h15 h16 h17 h18 hl h20

theorem LL_mapIdx_single (AR : Array IVec) :
    LL (AR.mapIdx fun i _ => #[i]) = (List.range AR.size).map fun i => [i] := by
  apply List.ext_getElem
  · simp [LL]
  · intro i h1 h2
    simp [LL]

@[expose] def emb3StepA (n : Nat) (A : Array (Array Int)) (e : Array (Array Nat)) (i : Nat) :
    Array (Array Nat) :=
  let c : Array Nat := Array.ofFn (n := n) fun j => imod3 A[j.val]![i]!
  if rank3 (e.push c) n > e.size then e.push c else e

theorem emb3Col_toList (n : Nat) (A : Array (Array Int)) (i : Nat) :
    (Array.ofFn (n := n) fun j => imod3 A[j.val]![i]!).toList =
      (List.range n).map fun j => imod3K (((LLI A).getD j []).getD i 0) := by
  apply List.ext_getElem
  · simp
  · intro j _ _
    simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    rw [imod3_eq, getElem!_eq_getD_toListI, getRowI]

@[expose] def emb3StepK (n : Nat) (Al : List (List Int)) (e : List (List Nat)) (i : Nat) :
    List (List Nat) :=
  if rank3K (e ++ [(List.range n).map fun j => imod3K ((Al.getD j []).getD i 0)]) n > e.length then
    e ++ [(List.range n).map fun j => imod3K ((Al.getD j []).getD i 0)]
  else e

theorem emb3_fold (n : Nat) (A : Array (Array Int)) : ∀ (l : List Nat) (e : Array (Array Nat)),
    (∀ r ∈ e.toList, r.size = n) →
    LL (l.foldl (emb3StepA n A) e) = l.foldl (emb3StepK n (LLI A)) (LL e) ∧
    ∀ r ∈ (l.foldl (emb3StepA n A) e).toList, r.size = n
  | [], _, h => ⟨rfl, h⟩
  | i :: l, e, h => by
    rw [List.foldl_cons, List.foldl_cons]
    have hc : (Array.ofFn (n := n) fun j => imod3 A[j.val]![i]!).size = n := by simp
    have hs : ∀ r ∈ (e.push (Array.ofFn (n := n) fun j => imod3 A[j.val]![i]!)).toList,
        r.size = n := by
      intro r hr
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h r hr
      · exact hc
    have e1 : LL (e.push (Array.ofFn (n := n) fun j => imod3 A[j.val]![i]!)) =
        LL e ++ [(List.range n).map fun j => imod3K (((LLI A).getD j []).getD i 0)] := by
      rw [LL, Array.toList_push, List.map_append, ← LL, List.map_singleton, emb3Col_toList]
    have hr : rank3 (e.push (Array.ofFn (n := n) fun j => imod3 A[j.val]![i]!)) n =
        rank3K (LL e ++ [(List.range n).map fun j => imod3K (((LLI A).getD j []).getD i 0)]) n := by
      rw [rank3_eq _ _ hs, e1]
    have hstep : LL (emb3StepA n A e i) = emb3StepK n (LLI A) (LL e) i ∧
        ∀ r ∈ (emb3StepA n A e i).toList, r.size = n := by
      unfold emb3StepA emb3StepK
      dsimp only
      rw [hr, length_LL]
      by_cases hc2 : rank3K (LL e ++ [(List.range n).map fun j =>
          imod3K (((LLI A).getD j []).getD i 0)]) n > e.size
      · rw [if_pos hc2, if_pos hc2]
        exact ⟨e1, hs⟩
      · rw [if_neg hc2, if_neg hc2]
        exact ⟨rfl, h⟩
    rw [← hstep.1]
    exact emb3_fold n A l _ hstep.2

theorem embLoop3_eq (n : Nat) (A : Array (Array Int)) : LL (embLoop 3 n A) = emb3K (LLI A) n := by
  unfold embLoop emb3K
  simp only [Nat.reduceBEq, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yieldL (emb3StepA n A) _ (fun i e => by
    unfold emb3StepA
    dsimp only
    split <;> rfl)]
  rw [bind_pure, ← List.range_eq_range']
  exact (emb3_fold n A _ #[] (by simp)).1

theorem std_eq (mode n : Nat) (A B : Array (Array Int)) (sc : Array Int) (emb : Array (Array Nat))
    (AR : Array IVec) (dk : DK) (Al : List (List Int)) (El : List (List Nat)) (hA : LLI A = Al)
    (hB : LLI B = bK Al sc.toList n) (hemb : LL emb = El) (hAR : LLI AR = toI dk.AR)
    (ht : tailOkK dk n (bK Al sc.toList n) = true) (hm : modeOkK dk mode n Al sc.toList El = true) :
    ∃ dt, tailS mode n AR (Array.ofFn (n := n) (·.val)) B (fhLoop mode n A B sc emb AR).1 AR
      (AR.mapIdx fun i _ => #[i]) (fhLoop mode n A B sc emb AR).2.1
      (fhLoop mode n A B sc emb AR).2.2 emb.size = some dt ∧ Rel dt dk := by
  simp only [modeOkK, Bool.and_eq_true, beq_iff_eq, and_assoc] at hm
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hm
  obtain ⟨e1, e2, e3⟩ := fhLoop_eq mode n A B sc emb AR
  rw [hA, hB, hemb, hAR, m6] at e1 e2 e3
  rw [e1]
  refine tailOk_tailS mode n AR _ B AR _ _ _ emb.size dk m1.symm ?_ ?_ hAR ?_ ?_ e2 e3 (by rw [hB]; exact ht)
  · rw [size_of_LL hemb, m5]
  · rw [hAR, m2]
  · rw [LL_mapIdx_single, size_of_LLI hAR, m3]
  · rw [ofFn_val_toList, m4]

end Certificates.GilmanCensusK

end
