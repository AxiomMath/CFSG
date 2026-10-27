module

public import CFSG.Certificates.InvariantMerge
public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.Schreier.Merge

public section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {n m : ℕ}

theorem mergeRel_equivalence (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (L : List (Fin m × Fin n × Fin n)) : ∀ k, Equivalence (mergeRel S b x L k)
  | 0 => Relation.EqvGen.is_equivalence _
  | k + 1 => by
    unfold mergeRel
    split
    · exact Relation.EqvGen.is_equivalence _
    · exact mergeRel_equivalence S b x L k

theorem mergeRel_mono {S : Fin m → Equiv.Perm (Fin n)} {b x : Fin n}
    {L : List (Fin m × Fin n × Fin n)} {k : ℕ} {a c : Fin n} (h : mergeRel S b x L k a c) :
    mergeRel S b x L (k + 1) a c := by
  rcases hk : L[k]? with _ | ⟨i, u, v⟩
  · simp only [mergeRel, hk]
    exact h
  · simp only [mergeRel, hk]
    exact Relation.EqvGen.rel _ _ (Or.inl h)

theorem relabel_size (lab : Array ℕ) (p q : ℕ) : (relabel lab p q).size = lab.size := by
  simp [relabel]

theorem relabel_get {lab : Array ℕ} {p q y : ℕ} (hy : y < lab.size) :
    (relabel lab p q)[y]! = if lab[y]! = lab[q]! then lab[p]! else lab[y]! := by
  unfold relabel
  rw [getElem!_pos _ y (by simpa using hy), Array.getElem_map, getElem!_pos lab y hy]
  simp only [beq_iff_eq]

theorem mergeInit_size (n b x : ℕ) : (mergeInit n b x).size = n := by simp [mergeInit]

theorem mergeInit_get {b x y : ℕ} (hy : y < n) :
    (mergeInit n b x)[y]! = if y = x then b else y := by
  rw [mergeInit, getElem!_pos _ y (by simpa using hy), Array.getElem_ofFn]

@[expose] def mergeVals (L : List (Fin m × Fin n × Fin n)) : List (ℕ × ℕ × ℕ) :=
  L.map fun t => ((t.1 : ℕ), (t.2.1 : ℕ), (t.2.2 : ℕ))

@[expose] def mergeState (n : ℕ) (G : Array (Array ℕ)) (b x : ℕ) (L : List (ℕ × ℕ × ℕ))
    (k : ℕ) : Bool × Array ℕ :=
  (L.take k).foldl (mergeStep n G) (true, mergeInit n b x)

theorem mergeState_succ {G : Array (Array ℕ)} {b x : ℕ} {L : List (ℕ × ℕ × ℕ)} {k : ℕ}
    (hk : k < L.length) :
    mergeState n G b x L (k + 1) = mergeStep n G (mergeState n G b x L k) L[k] := by
  rw [mergeState, mergeState, List.take_succ_eq_append_getElem hk, List.foldl_append]
  rfl

section State

variable {S : Fin m → Equiv.Perm (Fin n)} {G : Array (Array ℕ)} {b x : Fin n}
  {L : List (Fin m × Fin n × Fin n)}

theorem mergeState_size : ∀ k, (mergeState n G b x (mergeVals L) k).2.size = n
  | 0 => by simp [mergeState, mergeInit_size]
  | k + 1 => by
    by_cases hk : k < (mergeVals L).length
    · rw [mergeState_succ hk, mergeStep, relabel_size, mergeState_size k]
    · rw [mergeState, List.take_of_length_le (by omega), ← List.take_of_length_le
        (show (mergeVals L).length ≤ k by omega)]
      exact mergeState_size k

theorem mergeState_flag : ∀ k ≤ L.length, (mergeState n G b x (mergeVals L) k).1 = true →
    ∀ l < k, ∀ hl : l < L.length,
      (mergeState n G b x (mergeVals L) l).2[((L[l]).2.1 : ℕ)]! =
        (mergeState n G b x (mergeVals L) l).2[((L[l]).2.2 : ℕ)]!
  | 0, _, _, l, hl, _ => absurd hl (Nat.not_lt_zero l)
  | k + 1, hk, h, l, hl, hlL => by
    have hkL : k < L.length := by omega
    have hkV : k < (mergeVals L).length := by simpa [mergeVals] using hkL
    have hV : (mergeVals L)[k] = (((L[k]).1 : ℕ), ((L[k]).2.1 : ℕ), ((L[k]).2.2 : ℕ)) := by
      simp [mergeVals]
    rw [mergeState_succ hkV, mergeStep, hV] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hlk | rfl
    · exact mergeState_flag k (by omega) h.1.1.1.1 l hlk hlL
    · exact h.2

end State

section Merge

variable {S : Fin m → Equiv.Perm (Fin n)} {G : Array (Array ℕ)}
  (hrep : ∀ i : Fin m, Rep n G[(i : ℕ)]! (S i)) {b x : Fin n} {L : List (Fin m × Fin n × Fin n)}
include hrep

theorem mergeLabels_rel : ∀ k ≤ L.length, ∀ a c : Fin n,
    (mergeState n G b x (mergeVals L) k).2[(a : ℕ)]! =
      (mergeState n G b x (mergeVals L) k).2[(c : ℕ)]! → mergeRel S b x L k a c
  | 0, _, a, c, h => by
    simp only [mergeState, List.take_zero, List.foldl_nil] at h
    rw [mergeInit_get a.2, mergeInit_get c.2] at h
    have hR := mergeRel_equivalence S b x L 0
    have hbx : mergeRel S b x L 0 b x := Relation.EqvGen.rel _ _ ⟨rfl, rfl⟩
    by_cases ha : (a : ℕ) = x <;> by_cases hc : (c : ℕ) = x <;> simp only [ha, hc] at h
    · rw [Fin.ext ha, Fin.ext hc]; exact hR.refl _
    · rw [Fin.ext ha, show c = b from Fin.ext h.symm]; exact hR.symm hbx
    · rw [Fin.ext hc, show a = b from Fin.ext h]; exact hbx
    · rw [Fin.ext h]; exact hR.refl _
  | k + 1, hk, a, c, h => by
    have hkL : k < L.length := by omega
    have hkV : k < (mergeVals L).length := by simpa [mergeVals] using hkL
    have ih := mergeLabels_rel k (by omega)
    have hR := mergeRel_equivalence S b x L (k + 1)
    have hV : (mergeVals L)[k] = (((L[k]).1 : ℕ), ((L[k]).2.1 : ℕ), ((L[k]).2.2 : ℕ)) := by
      simp [mergeVals]
    rw [mergeState_succ hkV, mergeStep, hV] at h
    simp only at h
    have hsz : (mergeState n G b x (mergeVals L) k).2.size = n := mergeState_size k
    set lab := (mergeState n G b x (mergeVals L) k).2 with hlab
    set i := (L[k]).1
    set u := (L[k]).2.1
    set v := (L[k]).2.2
    have hp : (G[(i : ℕ)]!)[(u : ℕ)]! = ((S i u : Fin n) : ℕ) := hrep i u
    have hq : (G[(i : ℕ)]!)[(v : ℕ)]! = ((S i v : Fin n) : ℕ) := hrep i v
    rw [hp, hq, relabel_get (by rw [hsz]; exact a.2), relabel_get (by rw [hsz]; exact c.2)] at h
    have hnew : mergeRel S b x L (k + 1) (S i u) (S i v) := by
      rw [mergeRel_succ_of_lt hkL]
      exact Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
    by_cases ha : lab[(a : ℕ)]! = lab[((S i v : Fin n) : ℕ)]! <;>
      by_cases hc : lab[(c : ℕ)]! = lab[((S i v : Fin n) : ℕ)]! <;> simp only [ha, hc] at h
    · exact mergeRel_mono (ih a c (ha.trans hc.symm))
    ·
      exact hR.trans (mergeRel_mono (ih a _ ha)) (hR.trans (hR.symm hnew)
        (mergeRel_mono (ih _ c h)))
    · exact hR.trans (mergeRel_mono (ih a _ h))
        (hR.trans hnew (hR.symm (mergeRel_mono (ih c _ hc))))
    · exact mergeRel_mono (ih a c h)

theorem validInvariantMerge_of_mergeOK
    (h : mergeOK n G b x (mergeVals L) = true) : ValidInvariantMerge S b x L := by
  simp only [mergeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, -⟩, hflag⟩, hall⟩ := h
  have hlen : (mergeVals L).length = L.length := by simp [mergeVals]
  have hfin : mergeState n G b x (mergeVals L) L.length =
      (mergeVals L).foldl (mergeStep n G) (true, mergeInit n b x) := by
    rw [mergeState, List.take_of_length_le (by omega)]
  refine ⟨fun k hk => ?_, fun a c => ?_⟩
  · have hf : (mergeState n G b x (mergeVals L) L.length).1 = true := by rw [hfin]; exact hflag
    exact mergeLabels_rel hrep k (by omega) _ _
      (mergeState_flag L.length le_rfl hf k hk hk)
  · have hn : 0 < n := Fin.pos b
    have hR := mergeRel_equivalence S b x L L.length
    have h0 : ∀ y : Fin n, mergeRel S b x L L.length y ⟨0, hn⟩ := by
      intro y
      apply mergeLabels_rel hrep L.length le_rfl
      rw [hfin]
      have := allLt_spec hall y.2
      rwa [beq_iff_eq] at this
    exact hR.trans (h0 a) (hR.symm (h0 c))

end Merge

end CFSG.Certificates
