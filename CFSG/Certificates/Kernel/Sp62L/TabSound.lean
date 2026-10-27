module

public import CFSG.Certificates.Kernel.G2Three.BfsReplay
public import CFSG.Certificates.Kernel.G2Three.IndexMap
public import Certificates.Data.Kernel.Sp62L.Step

public section

namespace CFSG.KC.Sp62L

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U CFSG.KGroups.Sp6 CFSG.KC.G2Three

theorem getD_toArray {E : List (List ℕ)} {t : ℕ} (ht : t < E.length) :
    E.toArray.getD t [] = E[t] := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem ht]
  rfl

theorem inj_of_nodup {E : List (List ℕ)} (h : E.Nodup) :
    ∀ t < E.toArray.size, ∀ t' < E.toArray.size, E.toArray.getD t [] = E.toArray.getD t' [] →
      t = t' := by
  intro t ht t' ht' e
  rw [List.size_toArray] at ht ht'
  rw [getD_toArray ht, getD_toArray ht'] at e
  exact (h.getElem_inj_iff).1 e

theorem stepOK_of {gens : List (List ℕ)} {E : Array (List ℕ)} {P : Array (ℕ × ℕ)}
    {C POS : ℕ → ℕ} {hd s i : ℕ} (h : stepB gens E P C POS hd s i = true) :
    StepOK mulC gens E P C POS hd s i := by
  unfold stepB at h
  unfold StepOK
  by_cases hh : hd < C i
  · rw [if_pos hh] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
    refine ⟨fun _ => ⟨a, b, c, fun hp => ?_, fun hp => ?_⟩, fun hn => absurd hh hn⟩
    · rw [if_pos hp] at d
      simpa using d
    · rw [if_pos hp] at e
      simpa using e
  · rw [if_neg hh] at h
    exact ⟨fun h' => absurd h' hh, fun _ => by simpa using h⟩

theorem steps_of {gens : List (List ℕ)} {E : Array (List ℕ)} {P : Array (ℕ × ℕ)}
    {C POS : ℕ → ℕ} {fuel : ℕ} (h : stepsB gens E P C POS fuel = true) :
    ∀ hd < fuel, ∀ s < gens.length,
      StepOK mulC gens E P C POS hd s (hd * gens.length + s) := by
  intro hd hh s hs
  unfold stepsB at h
  rw [List.all_eq_true] at h
  have h2 := h hd (List.mem_range.2 hh)
  rw [List.all_eq_true] at h2
  exact stepOK_of (h2 s (List.mem_range.2 hs))

theorem tabOf_replay {gens : List (List ℕ)} {fuel : ℕ} {E : List (List ℕ)} {P : List (ℕ × ℕ)}
    {C POS : List ℕ} (hE0 : E.toArray.getD 0 [] = oneC) (hpos : 0 < E.length) (hnd : E.Nodup)
    (hPs : P.length + 1 = E.length) (hC0 : C.getD 0 0 = 1)
    (hs : stepsB gens E.toArray P.toArray (fun i => C.getD i 0) (fun i => POS.getD i 0) fuel = true)
    (hfin : C.getD (fuel * gens.length) 0 = E.length)
    (hb : build oneC mulC gens P = E.toArray) :
    tabOf gens fuel = E.toArray := by
  have hr := bfsParents_replay (one := oneC) (mul := mulC) (gens := gens) (fuel := fuel)
    (E := E.toArray) (P := P.toArray) (C := fun i => C.getD i 0) (POS := fun i => POS.getD i 0)
    hE0 (by rw [List.size_toArray]; exact hpos) (inj_of_nodup hnd)
    (by rw [List.size_toArray, List.size_toArray]; exact hPs) hC0 (steps_of hs)
    (by rw [List.size_toArray]; exact hfin)
  rw [tabOf, hr, List.toList_toArray, hb]

theorem closed_of {gens : List (List ℕ)} {E : List (List ℕ)} (h : closedB gens E = true) :
    ∀ v < E.toArray.size, ∀ g ∈ gens, ∃ t < E.toArray.size,
      E.toArray.getD t [] = mulC (E.toArray.getD v []) g := by
  intro v hv g hg
  unfold closedB at h
  rw [List.size_toArray] at hv ⊢
  have h1 := List.all_eq_true.1 h v (List.mem_range.2 hv)
  have h2 := List.all_eq_true.1 h1 g hg
  obtain ⟨t, ht, e⟩ := List.mem_iff_getElem.1 (List.elem_iff.1 h2)
  exact ⟨t, ht, by rw [getD_toArray ht, e]⟩

theorem tabCheck_of {gens : List (List ℕ)} {n : ℕ} {E : List (List ℕ)}
    {Pr : Array (List ℕ) → Bool} (htab : tabOf gens n = E.toArray) (hcl : closedB gens E = true)
    (hnd : E.Nodup)
    (hrest : (gens.all genB && E.toArray.size == n && allCheck validB E.toArray && Pr E.toArray) =
      true) :
    tabCheck gens n Pr = true := by
  dsimp only [tabCheck]
  rw [htab, closedCheck_of (closed_of hcl), distinctCheck_of (inj_of_nodup hnd), Bool.and_true,
    Bool.and_true]
  exact hrest

theorem of_replayB {gens : List (List ℕ)} {fuel : ℕ} {E : List (List ℕ)} {P : List (ℕ × ℕ)}
    {C POS : List ℕ} (h : replayB gens fuel E P C POS = true) :
    tabOf gens fuel = E.toArray ∧ closedB gens E = true ∧ E.Nodup := by
  unfold replayB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, hp⟩, hn⟩, hP⟩, hc⟩, hs⟩, hf⟩, hb⟩, hcl⟩ := h
  exact ⟨tabOf_replay h0 hp hn hP hc hs hf hb, hcl, hn⟩

end CFSG.KC.Sp62L

end
