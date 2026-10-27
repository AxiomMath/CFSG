module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def isInvol (ws : List (List (Fin m × Bool))) (i : Fin m) : Bool :=
  ws.contains [(i, true), (i, true)]

@[expose] def cols (ws : List (List (Fin m × Bool))) : List (Fin m × Bool) :=
  (List.finRange m).flatMap fun i =>
    if isInvol ws i then [(i, true)] else [(i, true), (i, false)]

@[expose] def colRep (ws : List (List (Fin m × Bool))) (x : Fin m × Bool) : Fin m × Bool :=
  if isInvol ws x.1 then (x.1, true) else x

@[expose] def colCode (ws : List (List (Fin m × Bool))) (x : Fin m × Bool) : ℕ :=
  (cols ws).idxOf (colRep ws x)

@[expose] def colCodes (ws us : List (List (Fin m × Bool))) : List (List ℕ) :=
  us.map (List.map (colCode ws))

@[expose] def colInv (ws : List (List (Fin m × Bool))) : Array ℕ :=
  ((cols ws).map fun x => colCode ws (x.1, !x.2)).toArray

noncomputable def colLetter (ws : List (List (Fin m × Bool))) (c : ℕ) : PG m ws :=
  match (cols ws)[c]? with
  | some x => PresentedGroup.mk _ (FreeGroup.mk [x])
  | none => 1

theorem mem_cols_of {ws : List (List (Fin m × Bool))} {x : Fin m × Bool}
    (h : isInvol ws x.1 = false ∨ x.2 = true) : x ∈ cols ws := by
  obtain ⟨i, b⟩ := x
  simp only [cols, List.mem_flatMap, List.mem_finRange, true_and]
  refine ⟨i, ?_⟩
  rcases h with h | h
  · simp only at h
    rw [h]
    cases b <;> simp
  · simp only at h
    subst h
    split <;> simp

theorem colRep_mem_cols (ws : List (List (Fin m × Bool))) (x : Fin m × Bool) :
    colRep ws x ∈ cols ws := by
  unfold colRep
  split
  · exact mem_cols_of (Or.inr rfl)
  · rename_i h
    exact mem_cols_of (Or.inl (by simpa using h))

theorem colCode_lt (ws : List (List (Fin m × Bool))) (x : Fin m × Bool) :
    colCode ws x < (cols ws).length :=
  List.idxOf_lt_length_of_mem (colRep_mem_cols ws x)

theorem getElem_colCode (ws : List (List (Fin m × Bool))) (x : Fin m × Bool) :
    (cols ws)[colCode ws x]'(colCode_lt ws x) = colRep ws x :=
  List.getElem_idxOf (colCode_lt ws x)

theorem mk_colRep (ws : List (List (Fin m × Bool))) (x : Fin m × Bool) :
    PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk [colRep ws x]) =
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk [x]) := by
  obtain ⟨i, b⟩ := x
  unfold colRep
  split
  · rename_i h
    cases b
    · have hsq : PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
          (FreeGroup.mk [(i, true), (i, true)]) = 1 :=
        PresentedGroup.one_of_mem (List.mem_map_of_mem (by simpa [isInvol] using h))
      have hsq' : (PresentedGroup.of i : PG m ws) * PresentedGroup.of i = 1 := hsq
      show (PresentedGroup.of i : PG m ws) = (PresentedGroup.of i)⁻¹
      exact (eq_inv_of_mul_eq_one_left hsq')
    · rfl
  · rfl

theorem colLetter_of_lt {ws : List (List (Fin m × Bool))} {c : ℕ} (hc : c < (cols ws).length) :
    colLetter ws c = PresentedGroup.mk _ (FreeGroup.mk [(cols ws)[c]]) := by
  unfold colLetter
  rw [List.getElem?_eq_getElem hc]

theorem colLetter_colCode (ws : List (List (Fin m × Bool))) (x : Fin m × Bool) :
    colLetter ws (colCode ws x) = PresentedGroup.mk _ (FreeGroup.mk [x]) := by
  rw [colLetter_of_lt (colCode_lt ws x), getElem_colCode, mk_colRep]

theorem evalWord_colCode (ws : List (List (Fin m × Bool))) (w : List (Fin m × Bool)) :
    evalWord (colLetter ws) (w.map (colCode ws)) = PresentedGroup.mk _ (FreeGroup.mk w) := by
  induction w with
  | nil => simp; rfl
  | cons x w ih =>
    rw [List.map_cons, evalWord_cons, ih, colLetter_colCode, ← map_mul, FreeGroup.mul_mk]
    rfl

theorem colInv_getD {ws : List (List (Fin m × Bool))} {c : ℕ} (hc : c < (cols ws).length) :
    (colInv ws).getD c 0 = colCode ws ((cols ws)[c].1, !(cols ws)[c].2) := by
  simp [colInv, Array.getD_eq_getD_getElem?, hc]

theorem colInv_lt {ws : List (List (Fin m × Bool))} {c : ℕ} (hc : c < (cols ws).length) :
    (colInv ws).getD c 0 < (cols ws).length := by
  rw [colInv_getD hc]
  exact colCode_lt ws _

theorem colLetter_colInv {ws : List (List (Fin m × Bool))} {c : ℕ}
    (hc : c < (cols ws).length) :
    colLetter ws ((colInv ws).getD c 0) = (colLetter ws c)⁻¹ := by
  rw [colInv_getD hc, colLetter_colCode, colLetter_of_lt hc]
  obtain ⟨i, b⟩ := (cols ws)[c]
  rw [← map_inv]
  cases b <;> rfl

theorem closure_colLetter (ws : List (List (Fin m × Bool))) :
    Subgroup.closure (colLetter ws '' Set.Iio (cols ws).length) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of]
  apply Subgroup.closure_le _ |>.mpr
  rintro _ ⟨i, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨colCode ws (i, true), colCode_lt ws _, ?_⟩
  rw [colLetter_colCode]
  rfl

theorem letters_colCodes {ws us : List (List (Fin m × Bool))} {w : List ℕ}
    (hw : w ∈ colCodes ws us) : ∀ y ∈ w, y < (cols ws).length := by
  simp only [colCodes, List.mem_map] at hw
  obtain ⟨v, -, rfl⟩ := hw
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨x, -, rfl⟩ := hy
  exact colCode_lt ws x

theorem colCodes_facts (ws : List (List (Fin m × Bool))) {r : List ℕ}
    (hr : r ∈ colCodes ws ws ++ (colCodes ws ws).map (invWord (colInv ws))) :
    (∀ y ∈ r, y < (cols ws).length) ∧ evalWord (colLetter ws) r = 1 := by
  have hrel : ∀ r ∈ colCodes ws ws, evalWord (colLetter ws) r = 1 := by
    intro r hr
    simp only [colCodes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rw [evalWord_colCode]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hv)
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨letters_colCodes hr, hrel r hr⟩
  · simp only [List.mem_map] at hr
    obtain ⟨r0, hr0, rfl⟩ := hr
    have hl := letters_colCodes hr0
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [invWord, List.mem_map, List.mem_reverse] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact colInv_lt (hl z hz)
    · rw [evalWord_invWord (fun y hy => colLetter_colInv (hl y hy)), hrel r0 hr0, inv_one]

@[expose] def colParams (ws subs : List (List (Fin m × Bool))) : Params :=
  mkParams (cols ws).length (colInv ws) (colCodes ws ws) (colCodes ws subs)

@[expose] def colParamsShort (ws subs : List (List (Fin m × Bool))) (k : ℕ) : Params :=
  { mkParams (cols ws).length (colInv ws) ((colCodes ws ws).filter fun w => w.length ≤ k)
      (colCodes ws subs) with
    rels := (colCodes ws ws).map fun w => (w, invWord (colInv ws) w) }

theorem good_subs_rels (ws subs : List (List (Fin m × Bool))) (H : Subgroup (PG m ws))
    (hsubs : ∀ w ∈ subs, PresentedGroup.mk _ (FreeGroup.mk w) ∈ H) :
    (∀ p ∈ (colCodes ws subs).map (fun w => (w, invWord (colInv ws) w)),
      p.2 = invWord (colInv ws) p.1 ∧ (∀ y ∈ p.1, y < (cols ws).length) ∧
        evalWord (colLetter ws) p.1 ∈ H) ∧
    (∀ p ∈ (colCodes ws ws).map (fun w => (w, invWord (colInv ws) w)),
      p.2 = invWord (colInv ws) p.1 ∧ (∀ y ∈ p.1, y < (cols ws).length) ∧
        evalWord (colLetter ws) p.1 = 1) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨w, hw, rfl⟩ := hp
    refine ⟨rfl, letters_colCodes hw, ?_⟩
    simp only [colCodes, List.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [evalWord_colCode]
    exact hsubs v hv
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨w, hw, rfl⟩ := hp
    exact ⟨rfl, letters_colCodes hw, (colCodes_facts ws (List.mem_append_left _ hw)).2⟩

theorem goodColParams (ws subs : List (List (Fin m × Bool))) (H : Subgroup (PG m ws))
    (hsubs : ∀ w ∈ subs, PresentedGroup.mk _ (FreeGroup.mk w) ∈ H) :
    Good (colLetter ws) H (colParams ws subs) := by
  obtain ⟨hs, hr⟩ := good_subs_rels ws subs H hsubs
  refine ⟨fun x hx => colInv_lt hx, fun x hx => colLetter_colInv hx, ?_, hs, hr⟩
  intro x p hp
  obtain ⟨h1, r, hr', hpr⟩ := mem_scans hp
  obtain ⟨hl, he⟩ := colCodes_facts ws hr'
  exact ⟨h1, letters_rotation hpr hl, evalWord_rotation hpr he⟩

theorem goodColParamsShort (ws subs : List (List (Fin m × Bool))) (k : ℕ)
    (H : Subgroup (PG m ws)) (hsubs : ∀ w ∈ subs, PresentedGroup.mk _ (FreeGroup.mk w) ∈ H) :
    Good (colLetter ws) H (colParamsShort ws subs k) := by
  obtain ⟨hs, hr⟩ := good_subs_rels ws subs H hsubs
  refine ⟨fun x hx => colInv_lt hx, fun x hx => colLetter_colInv hx, ?_, hs, hr⟩
  intro x p hp
  obtain ⟨h1, r, hr', hpr⟩ := mem_scans (L := (cols ws).length) (inv := colInv ws)
    (rels := (colCodes ws ws).filter fun w => w.length ≤ k) (subs := colCodes ws subs) hp
  have hr'' : r ∈ colCodes ws ws ++ (colCodes ws ws).map (invWord (colInv ws)) := by
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact List.mem_append_left _ (List.mem_of_mem_filter hr')
    · simp only [List.mem_map] at hr'
      obtain ⟨r0, hr0, rfl⟩ := hr'
      exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_mem_filter hr0))
  obtain ⟨hl, he⟩ := colCodes_facts ws hr''
  exact ⟨h1, letters_rotation hpr hl, evalWord_rotation hpr he⟩

theorem card_le_of_genSub_index (ws : List (List (Fin m × Bool))) (S : List (Fin m)) {n : ℕ}
    (hfi : (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S).FiniteIndex)
    (hidx : (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S).index ≤ n)
    [Finite (PG S.length (restrictWords S ws))] :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * Nat.card (PG S.length (restrictWords S ws)) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  obtain ⟨hfinH, hsub⟩ := card_genSub_le ws S
  have hfin : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ genSub rels S) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (genSub rels S)
  refine ⟨hfin, ?_⟩
  rw [← (genSub rels S).index_mul_card]
  exact Nat.mul_le_mul hidx hsub

theorem genSub_words_mem (ws : List (List (Fin m × Bool))) (S : List (Fin m)) :
    ∀ w ∈ S.map (fun x => [(x, true)]), PresentedGroup.mk _ (FreeGroup.mk w) ∈
      genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S := by
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  exact Subgroup.subset_closure ⟨x, hx, rfl⟩

@[expose] def subsetCheckC (ws : List (List (Fin m × Bool))) (S : List ℕ) (cap n : ℕ) : Bool :=
  check (colParams ws ((subsetOf m S).map fun x => [(x, true)])) cap n

@[expose] def subsetCheckShortC (ws : List (List (Fin m × Bool))) (S : List ℕ) (k cap n : ℕ) :
    Bool :=
  checkHLT (colParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k) cap n

theorem card_le_of_subsetCheckC (ws : List (List (Fin m × Bool))) (S : List ℕ) {cap n : ℕ}
    (h : subsetCheckC ws S cap n = true)
    [Finite (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws))] :
    Finite (PG m ws) ∧
      Nat.card (PG m ws) ≤ n * Nat.card (PG (subsetOf m S).length
        (restrictWords (subsetOf m S) ws)) := by
  obtain ⟨hfi, hidx⟩ := index_le_of_check
    (goodColParams ws _ _ (genSub_words_mem ws (subsetOf m S)))
    (by simpa [colParams, mkParams] using closure_colLetter ws) h
  exact card_le_of_genSub_index ws (subsetOf m S) hfi hidx

theorem card_le_of_subsetCheckShortC (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {k cap n : ℕ} (h : subsetCheckShortC ws S k cap n = true)
    [Finite (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws))] :
    Finite (PG m ws) ∧
      Nat.card (PG m ws) ≤ n * Nat.card (PG (subsetOf m S).length
        (restrictWords (subsetOf m S) ws)) := by
  obtain ⟨hfi, hidx⟩ := index_le_of_checkHLT
    (goodColParamsShort ws _ k _ (genSub_words_mem ws (subsetOf m S)))
    (by simpa [colParamsShort, mkParams] using closure_colLetter ws) h
  exact card_le_of_genSub_index ws (subsetOf m S) hfi hidx

theorem card_le_of_subsetCheckC_nil (ws : List (List (Fin m × Bool))) {cap n : ℕ}
    (h : subsetCheckC ws [] cap n = true) : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have hS : subsetOf m [] = [] := by simp [subsetOf]
  have : Finite (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) := by
    rw [hS]; exact (inferInstance : Finite (PG 0 _))
  have hc : Nat.card (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) = 1 := by
    rw [hS]; exact card_PG_zero _
  have := card_le_of_subsetCheckC ws [] h
  rwa [hc, mul_one] at this

end CFSG.CosetTable
