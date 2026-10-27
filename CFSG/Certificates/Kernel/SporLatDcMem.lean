module

public import CFSG.Certificates.Kernel.SporLatDcStab

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

theorem evalElt_append (a b : List ℕ) :
    evalElt P.els (a ++ b) = evalElt P.els a * evalElt P.els b := by
  simp [evalElt, List.map_append, List.prod_append]

private theorem getD_map_evalElt (E : List (List ℕ)) (i : ℕ) :
    (E.map (evalElt P.els)).getD i 1 = evalElt P.els (E.getD i []) := by
  rcases Nat.lt_or_ge i E.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h),
      List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    rfl

private def wordEltList (E : List (List ℕ)) (u : List ℕ) : Γ :=
  (u.map fun i => (E.map (evalElt P.els)).getD i 1).prod

private def wordOfE (E : List (List ℕ)) (u : List ℕ) : List ℕ :=
  u.flatMap fun i => E.getD i []

private theorem wordOfE_letters {E : List (List ℕ)} (hE : ∀ w ∈ E, ∀ l ∈ w, l < 2 + P.C.ns)
    {u : List ℕ} (hu : ∀ i ∈ u, i < E.length) :
    ∀ l ∈ wordOfE E u, l < 2 + P.C.ns := by
  intro l hl
  rw [wordOfE, List.mem_flatMap] at hl
  obtain ⟨i, -, hli⟩ := hl
  rcases Nat.lt_or_ge i E.length with h | h
  · exact hE (E.getD i []) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      exact List.getElem_mem h) l hli
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at hli
    exact absurd hli (by simp)

private theorem wordE_act {E : List (List ℕ)} (hE : ∀ w ∈ E, ∀ l ∈ w, l < 2 + P.C.ns) :
    ∀ (u : List ℕ), (∀ i ∈ u, i < E.length) → ∀ p < n,
      wordE P.C.L E u p = act n (P.wordEltList E u) p ∧ wordE P.C.L E u p < n := by
  intro u
  induction u with
  | nil =>
    intro _ p hp
    rw [wordE, List.foldr_nil, wordEltList, List.map_nil, List.prod_nil]
    exact ⟨(act_one hp).symm, hp⟩
  | cons i u ih =>
    intro hu p hp
    obtain ⟨he, hlt⟩ := ih (fun i' hi' => hu i' (List.mem_cons_of_mem _ hi')) p hp
    have hletters : ∀ l ∈ E.getD i [], l < 2 + P.C.ns := by
      rcases Nat.lt_or_ge i E.length with hi | hi
      · exact hE (E.getD i []) (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          exact List.getElem_mem hi)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
        intro l hl
        exact absurd hl (by simp)
    have hact : act n (P.wordEltList E u) p < n := by rw [← he]; exact hlt
    obtain ⟨hwf, hwflt⟩ := P.act_wordF (E.getD i []) hletters (act n (P.wordEltList E u) p) hact
    have hgoal : wordE P.C.L E (i :: u) p =
        wordF P.C.L (E.getD i []) (wordE P.C.L E u p) := rfl
    have hwf' : act n (evalElt P.els (E.getD i [])) (wordE P.C.L E u p) =
        wordF P.C.L (E.getD i []) (wordE P.C.L E u p) := by rw [he]; exact hwf
    have hwflt' : wordF P.C.L (E.getD i []) (wordE P.C.L E u p) < n := by
      rw [he]; exact hwflt
    have hR : P.wordEltList E (i :: u) =
        (E.map (evalElt P.els)).getD i 1 * P.wordEltList E u := rfl
    rw [hgoal, hR, P.getD_map_evalElt, act_mul _ _ hp, ← he]
    exact ⟨hwf'.symm, hwflt'⟩

private theorem memW_spec {E : List (List ℕ)} {x : Wit} {T : List ℕ} (h : memW P.C E x T = true) :
    (∀ i ∈ x.1, i < E.length) ∧ isS P.C x.2.1 = true ∧
      labF (fun p => wordF P.C.L x.2.1 (wordE P.C.L E x.1 p)) P.C.Δ = T := by
  unfold memW at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨?_, h.1.2, ?_⟩
  · intro i hi
    have h1 := (List.all_eq_true.mp h.1.1) i hi
    rw [Nat.blt_eq] at h1
    exact h1
  · simpa using h.2

private theorem memW_lab {E : List (List ℕ)} (hE : ∀ w ∈ E, ∀ l ∈ w, l < 2 + P.C.ns)
    {s : List ℕ} (hs : ∀ l ∈ s, l < 2 + P.C.ns) {u : List ℕ}
    (hu : ∀ i ∈ u, i < E.length) :
    lab n ptLab P.C.Δ (evalElt P.els s * P.wordEltList E u) =
      labF (fun p => wordF P.C.L s (wordE P.C.L E u p)) P.C.Δ := by
  have hΔ := P.hΔ
  have hu' : P.wordEltList E u = evalElt P.els (wordOfE E u) := by
    rw [wordEltList]
    induction u with
    | nil => simp [wordOfE, evalElt]
    | cons i u ih =>
      rw [List.map_cons, List.prod_cons, wordOfE, List.flatMap_cons, P.evalElt_append,
        P.getD_map_evalElt, ih (fun i hi => hu i (List.mem_cons_of_mem _ hi))]
      rfl
  have hpt : ptAct (tab n (evalElt P.els s)).toArray
      (lab n ptLab P.C.Δ (evalElt P.els (wordOfE E u))) =
      sortN (P.C.Δ.map fun p => act n (evalElt P.els s * P.wordEltList E u) p) := by
    rw [ptAct_tab]
    change sortN (List.map (fun p => act n (evalElt P.els s) p)
      (ptAct (tab n (evalElt P.els (wordOfE E u))).toArray P.C.Δ)) =
      sortN (List.map (fun p => act n (evalElt P.els s * P.wordEltList E u) p) P.C.Δ)
    rw [ptAct_tab, sortN_map_sortN, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    rw [← hu', act_mul _ _ (hΔ.2 p hp)]
    rfl
  have hr : labF (fun p => wordF P.C.L s (wordE P.C.L E u p)) P.C.Δ =
      sortN (P.C.Δ.map fun p => act n (evalElt P.els s * P.wordEltList E u) p) := by
    rw [labF, ← CFSG.KC.E64F.sortN_eq]
    congr 1
    apply List.map_congr_left
    intro p hp
    have hwu := P.wordE_act hE u hu p (hΔ.2 p hp)
    calc wordF P.C.L s (wordE P.C.L E u p)
        = act n (evalElt P.els s) (wordE P.C.L E u p) :=
          (P.act_wordF_eq hs hwu.2).symm
      _ = act n (evalElt P.els s) (act n (P.wordEltList E u) p) := by rw [hwu.1]
      _ = act n (evalElt P.els s * P.wordEltList E u) p :=
          (act_mul _ _ (hΔ.2 p hp)).symm
  rw [hu', lab_mul hlaw hΔ]
  exact hpt.trans hr.symm

theorem memW_sound {E : List (List ℕ)} (hE : ∀ w ∈ E, ∀ l ∈ w, l < 2 + P.C.ns)
    {x : Wit} {T : List ℕ} (h : memW P.C E x T = true) :
    ∃ s ∈ P.S, ∃ u : Γ, u ∈ Subgroup.closure {y | ∃ w ∈ E, y = evalElt P.els w} ∧
      lab n ptLab P.C.Δ (s * u) = T := by
  obtain ⟨hu, hisS, hlab⟩ := memW_spec P h
  refine ⟨evalElt P.els x.2.1, evalElt_mem_S P (isS_spec P hisS), P.wordEltList E x.1, ?_, ?_⟩
  · apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    rw [P.getD_map_evalElt]
    rcases Nat.lt_or_ge i E.length with hi' | hi'
    · apply Subgroup.subset_closure
      refine ⟨E.getD i [], ?_, rfl⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      exact List.getElem_mem hi'
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi']
      exact Subgroup.one_mem _
  · rw [memW_lab P hE (isS_lt P hisS) hu, hlab]

end DcSoundCtx

end CFSG.KC.SLDc

end
