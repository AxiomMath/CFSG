module

public import CFSG.Certificates.Kernel.SporLatDcSortSound

public section

namespace CFSG.KC.SLDc

theorem getElem_slice {α : Type} {l : List α} {s i : Nat} (hs : 0 < s) (hi : i < l.length) :
    ∃ h : i % s < ((l.drop (s * (i / s))).take s).length,
      ((l.drop (s * (i / s))).take s)[i % s] = l[i] := by
  have e : s * (i / s) + i % s = i := Nat.div_add_mod i s
  have hm := Nat.mod_lt i hs
  refine ⟨by simp only [List.length_take, List.length_drop]; omega, ?_⟩
  simp only [List.getElem_take, List.getElem_drop, e]

theorem div_lt_of_slices {s m i : Nat} (hi : i < s * m) : i / s < m := by
  rcases Nat.lt_or_ge (i / s) m with h | h
  · exact h
  · have := Nat.mul_le_mul_left s h
    have := Nat.mul_div_le i s
    omega

theorem all_of_slices {α : Type} {g : α → Bool} {l : List α} {s m : Nat} (hs : 0 < s)
    (hl : l.length ≤ s * m) (h : ∀ j < m, ((l.drop (s * j)).take s).all g = true) :
    l.all g = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨hk, e⟩ := getElem_slice hs hi
  have := List.all_eq_true.1 (h (i / s) (div_lt_of_slices (by omega))) _ (List.getElem_mem hk)
  rwa [e] at this

theorem allIdx_of_slices {α : Type} {f : Nat → α → Bool} {c : Nat} {l : List α} {s m : Nat}
    (hs : 0 < s) (hl : l.length ≤ s * m)
    (h : ∀ j < m, allIdx f (c + s * j) ((l.drop (s * j)).take s) = true) :
    allIdx f c l = true := by
  rw [allIdx_iff]
  intro i hi
  obtain ⟨hk, e⟩ := getElem_slice hs hi
  have := (allIdx_iff f _ _).1 (h (i / s) (div_lt_of_slices (by omega))) _ hk
  rwa [e, Nat.add_assoc, Nat.div_add_mod] at this

theorem sortedLt_iff_adj : ∀ l : List (List Nat),
    sortedLt l = true ↔ ∀ i (h : i + 1 < l.length), lexLt l[i] l[i + 1] = true
  | [] => by simp [sortedLt]
  | [_] => by simp [sortedLt]
  | a :: b :: l => by
    rw [show sortedLt (a :: b :: l) = (lexLt a b && sortedLt (b :: l)) from rfl, Bool.and_eq_true,
      sortedLt_iff_adj (b :: l)]
    constructor
    · rintro ⟨h0, h⟩ i hi
      rcases i with _ | i
      · exact h0
      · simp only [List.getElem_cons_succ]
        exact h i (by simp only [List.length_cons] at hi ⊢; omega)
    · intro h
      refine ⟨h 0 (by simp), fun i hi => ?_⟩
      have := h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
      simp only [List.getElem_cons_succ] at this
      exact this

theorem getElem_drop_take {α : Type} {l : List α} {k t j : Nat} (hj : j < t)
    (hk : k + j < l.length) :
    ∃ h : j < ((l.drop k).take t).length, ((l.drop k).take t)[j] = l[k + j] :=
  ⟨by simp only [List.length_take, List.length_drop]; omega, by
    simp only [List.getElem_take, List.getElem_drop]⟩

theorem sortedLt_of_slices {l : List (List Nat)} {s m : Nat} (hs : 0 < s)
    (hl : l.length ≤ s * m + 1) (h : ∀ j < m, sortedLt ((l.drop (s * j)).take (s + 1)) = true) :
    sortedLt l = true := by
  rw [sortedLt_iff_adj]
  intro i hi
  have e : s * (i / s) + i % s = i := Nat.div_add_mod i s
  have hm := Nat.mod_lt i hs
  obtain ⟨h1, e1⟩ := getElem_drop_take (l := l) (k := s * (i / s)) (t := s + 1) (j := i % s)
    (by omega) (by omega)
  obtain ⟨h2, e2⟩ := getElem_drop_take (l := l) (k := s * (i / s)) (t := s + 1) (j := i % s + 1)
    (by omega) (by omega)
  have hr := (sortedLt_iff_adj _).1 (h (i / s) (div_lt_of_slices (by omega))) (i % s) h2
  have e1' : l[s * (i / s) + i % s] = l[i] := by simp only [e]
  have e2' : l[s * (i / s) + (i % s + 1)] = l[i + 1] := by
    simp only [show s * (i / s) + (i % s + 1) = i + 1 by omega]
  rw [e1, e2, e1', e2'] at hr
  exact hr

theorem omC_of_parts {actF : Nat → List Nat → List Nat} {x0 : List Nat} {nl B : Nat}
    {C : List (List (List Nat))} {rows : List (List Nat)} {par via ord : List Nat}
    (h1 : (chunksOK B C && (C.flatten.headD [] == x0) && Nat.beq rows.length nl) = true)
    (h2 : ∀ l < nl, Nat.beq (rows.getD l []).length C.flatten.length = true)
    (h3 : ∀ l < nl, ((List.zip (rows.getD l []) C.flatten).all fun e =>
      Nat.blt e.1 C.flatten.length && lookC B C e.1 == actF l e.2) = true)
    (h4 : (Nat.beq par.length C.flatten.length && Nat.beq via.length C.flatten.length) = true)
    (h5 : allIdx (fun i e => Nat.beq i 0 ||
      (Nat.blt e.1.1 i && Nat.blt e.1.2 nl && actF e.1.2 (lookC B C e.1.1) == e.2)) 0
      (List.zip (List.zip par via) C.flatten) = true)
    (h6 : (Nat.beq ord.length C.flatten.length && ord.all (fun i => Nat.blt i C.flatten.length)) =
      true)
    (h7 : sortedLt (ord.map (lookC B C)) = true) :
    omC actF x0 nl B C rows par via ord = true := by
  simp only [Bool.and_eq_true] at h1 h4 h6
  have hn : rows.length = nl := Nat.eq_of_beq_eq_true h1.2
  have hrows : allIdx (fun l row => Nat.beq row.length C.flatten.length &&
      (List.zip row C.flatten).all fun e =>
        Nat.blt e.1 C.flatten.length && lookC B C e.1 == actF l e.2) 0 rows = true := by
    rw [allIdx_iff]
    intro i hi
    rw [Nat.zero_add, Bool.and_eq_true, ← List.getD_eq_getElem _ []]
    exact ⟨h2 i (hn ▸ hi), h3 i (hn ▸ hi)⟩
  unfold omC
  rw [h1.1.1, h1.1.2, h1.2, hrows, h4.1, h4.2, h5, h6.1, h6.2, h7]
  rfl

end CFSG.KC.SLDc

end
