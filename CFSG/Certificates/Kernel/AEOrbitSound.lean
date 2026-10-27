module

public import Certificates.Data.Kernel.AEOrbitK

public section

namespace CFSG.KC.AEOrbitK

open Certificates.AEOrbit

variable {m : ℕ}

theorem testBit_imgM : ∀ (t : List ℕ) (M j : ℕ),
    (imgM t M).testBit j = true ↔ ∃ i, ∃ h : i < t.length, M.testBit i = true ∧ t[i] = j
  | [], M, j => by simp [imgM]
  | a :: t, M, j => by
    rw [imgM, Nat.testBit_or, Bool.or_eq_true, testBit_imgM t (M / 2) j]
    constructor
    · rintro (h | ⟨i, hi, h1, h2⟩)
      · split at h
        · rename_i hM
          rw [Nat.testBit_two_pow, decide_eq_true_eq] at h
          refine ⟨0, by simp, ?_, by simpa using h⟩
          rw [Nat.testBit_zero]
          simpa using hM
        · simp at h
      · refine ⟨i + 1, by simpa using hi, ?_, by simpa using h2⟩
        rwa [Nat.testBit_succ]
    · rintro ⟨i, hi, h1, h2⟩
      cases i with
      | zero =>
        left
        have hM : M % 2 = 1 := by
          rw [Nat.testBit_zero] at h1
          simpa using h1
        rw [if_pos hM, Nat.testBit_two_pow, decide_eq_true_eq]
        simpa using h2
      | succ i =>
        right
        exact ⟨i, by simpa using hi, by rwa [← Nat.testBit_succ], by simpa using h2⟩

theorem dec_imgM (σ : Equiv.Perm (Fin m)) (M : ℕ) :
    dec m (imgM (tab σ) M) = (dec m M).image σ := by
  ext j
  simp only [dec, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    testBit_imgM, tab, List.length_map, List.length_finRange, List.getElem_map,
    List.getElem_finRange]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨⟨i, hi⟩, h1, Fin.ext (by simpa using h2)⟩
  · rintro ⟨i, h1, rfl⟩
    exact ⟨i, i.isLt, h1, rfl⟩

theorem imgM_lt : ∀ (t : List ℕ) (M : ℕ), (∀ a ∈ t, a < m) → imgM t M < 2 ^ m
  | [], _, _ => by simp [imgM]
  | a :: t, M, ht => by
    rw [imgM]
    apply Nat.or_lt_two_pow
    · split
      · exact Nat.pow_lt_pow_right (by norm_num) (ht a List.mem_cons_self)
      · exact Nat.two_pow_pos m
    · exact imgM_lt t (M / 2) fun b hb => ht b (List.mem_cons_of_mem _ hb)

theorem tab_lt (σ : Equiv.Perm (Fin m)) : ∀ a ∈ tab σ, a < m := by
  intro a ha
  simp only [tab, List.mem_map] at ha
  obtain ⟨i, -, rfl⟩ := ha
  exact (σ i).isLt

theorem movesT_sub (hs : ∀ σ ∈ cands m, Equiv.Perm.sign σ = 1) {a : ℕ} (ha : a < 2 ^ m) :
    ∀ t ∈ movesT ((cands m).map tab) a, ∃ σ ∈ moves m (dec m a), t = tab σ := by
  intro t ht
  simp only [movesT, List.mem_filter, List.mem_map, beq_iff_eq] at ht
  obtain ⟨⟨σ, hσ, rfl⟩, he⟩ := ht
  refine ⟨σ, ?_, rfl⟩
  simp only [moves, List.mem_filter, decide_eq_true_eq]
  refine ⟨hσ, hs σ hσ, ?_⟩
  rw [← dec_imgM, he]

theorem image_mem_step {L : List (Equiv.Perm (Fin m))} {S : Finset (Finset (Fin m))}
    {γ : Finset (Fin m)} {σ : Equiv.Perm (Fin m)} (hγ : γ ∈ S) (hσ : σ ∈ L) :
    γ.image σ ∈ step L S := by
  unfold step
  simp only [Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_map]
  exact Or.inr ⟨γ, hγ, σ, hσ, rfl⟩

@[expose] def TabsOf (LT : List (List ℕ)) (L : List (Equiv.Perm (Fin m))) : Prop :=
  ∀ t ∈ LT, ∃ σ ∈ L, t = tab σ

@[expose] def Good (T : Finset (Finset (Fin m))) (acc : List ℕ) : Prop :=
  ∀ x ∈ acc, x < 2 ^ m ∧ dec m x ∈ T

theorem addM_good {LT : List (List ℕ)} {L : List (Equiv.Perm (Fin m))} (hL : TabsOf LT L)
    {R : Finset (Finset (Fin m))} {x : ℕ} (hx : dec m x ∈ R) :
    ∀ st : List ℕ × List ℕ, Good (step L R) st.1 → Good (step L R) st.2 →
      Good (step L R) (addM LT st x).1 ∧ Good (step L R) (addM LT st x).2 := by
  induction LT with
  | nil => exact fun st h1 h2 => ⟨h1, h2⟩
  | cons t LT ih =>
    intro st h1 h2
    have e : addM (t :: LT) st x = addM LT
        (if imgM t x ∈ st.1 then st else (imgM t x :: st.1, imgM t x :: st.2)) x := rfl
    rw [e]
    refine ih (fun t' ht' => hL t' (List.mem_cons_of_mem _ ht')) _ ?_ ?_ <;> split
    · exact h1
    · obtain ⟨σ, hσ, rfl⟩ := hL t List.mem_cons_self
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨imgM_lt _ _ (tab_lt σ), by rw [dec_imgM]; exact image_mem_step hx hσ⟩
      · exact h1 y hy
    · exact h2
    · obtain ⟨σ, hσ, rfl⟩ := hL t List.mem_cons_self
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨imgM_lt _ _ (tab_lt σ), by rw [dec_imgM]; exact image_mem_step hx hσ⟩
      · exact h2 y hy

theorem foldl_addM_good {LT : List (List ℕ)} {L : List (Equiv.Perm (Fin m))} (hL : TabsOf LT L)
    {R : Finset (Finset (Fin m))} :
    ∀ (S : List ℕ) (st : List ℕ × List ℕ), Good R S → Good (step L R) st.1 →
      Good (step L R) st.2 →
      Good (step L R) (S.foldl (addM LT) st).1 ∧ Good (step L R) (S.foldl (addM LT) st).2
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | x :: S, st, hS, h1, h2 => by
    rw [List.foldl_cons]
    have h := addM_good hL (hS x List.mem_cons_self).2 st h1 h2
    exact foldl_addM_good hL S _ (fun y hy => hS y (List.mem_cons_of_mem _ hy)) h.1 h.2

theorem reachM_good {LT : List (List ℕ)} {α β : Finset (Fin m)}
    (hL : TabsOf LT (moves m α ++ moves m β)) {a : ℕ} (ha : a < 2 ^ m) (hα : dec m a = α) :
    ∀ n, Good (reach m α β n) (reachM LT a n).1 ∧ Good (reach m α β n) (reachM LT a n).2
  | 0 => by
    have h : Good (reach m α β 0) [a] := by
      intro x hx
      rw [List.mem_singleton.1 hx, hα]
      exact ⟨ha, Finset.mem_singleton_self α⟩
    exact ⟨h, h⟩
  | n + 1 => by
    have ih := reachM_good hL ha hα n
    refine foldl_addM_good hL _ _ (fun x hx => (ih.2 x hx)) ?_ (fun _ hx => by simp at hx)
    intro x hx
    obtain ⟨h1, h2⟩ := ih.1 x hx
    exact ⟨h1, Finset.mem_union_left _ h2⟩

theorem reach_sub_fours {α : Finset (Fin m)} (hα : α ∈ fours m) (β : Finset (Fin m)) :
    ∀ n, reach m α β n ⊆ fours m
  | 0 => by
    intro x hx
    rw [Finset.mem_singleton.1 hx]
    exact hα
  | n + 1 => by
    intro x hx
    have ih := reach_sub_fours hα β n
    change x ∈ step _ _ at hx
    unfold step at hx
    simp only [Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_map] at hx
    rcases hx with hx | ⟨γ, hγ, σ, -, rfl⟩
    · exact ih hx
    · have h4 := ih hγ
      unfold fours at h4 ⊢
      rw [Finset.mem_powersetCard] at h4 ⊢
      exact ⟨Finset.subset_univ _, (Finset.card_image_of_injective γ σ.injective).trans h4.2⟩

theorem reach_eq_of (hs : ∀ σ ∈ cands m, Equiv.Perm.sign σ = 1)
    (h : kchkM m ((cands m).map tab) 4 = true) (hlt : ∀ a ∈ masks4 m, a < 2 ^ m)
    (hf : ∀ α ∈ fours m, ∃ a ∈ masks4 m, dec m a = α) :
    ∀ α ∈ fours m, ∀ β ∈ fours m, α ≠ β → reach m α β 4 = fours m := by
  intro α hα β hβ hne
  refine Finset.Subset.antisymm (reach_sub_fours hα β 4) fun γ hγ => ?_
  obtain ⟨a, ha, rfl⟩ := hf α hα
  obtain ⟨b, hb, rfl⟩ := hf β hβ
  obtain ⟨c, hc, rfl⟩ := hf γ hγ
  unfold kchkM at h
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h a ha b hb with h1 | h1
  · exact absurd (congrArg (dec m) h1) hne
  · have hL : TabsOf (movesT ((cands m).map tab) a ++ movesT ((cands m).map tab) b)
        (moves m (dec m a) ++ moves m (dec m b)) := by
      intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨σ, hσ, e⟩ := movesT_sub hs (hlt a ha) t ht
        exact ⟨σ, List.mem_append_left _ hσ, e⟩
      · obtain ⟨σ, hσ, e⟩ := movesT_sub hs (hlt b hb) t ht
        exact ⟨σ, List.mem_append_right _ hσ, e⟩
    exact ((reachM_good hL (hlt a ha) rfl 4).1 c (h1 c hc)).2

theorem check_of (hs5 : ∀ σ ∈ cands 5, Equiv.Perm.sign σ = 1)
    (hs6 : ∀ σ ∈ cands 6, Equiv.Perm.sign σ = 1)
    (h5 : kchkM 5 ((cands 5).map tab) 4 = true) (h6 : kchkM 6 ((cands 6).map tab) 4 = true)
    (hl5 : ∀ a ∈ masks4 5, a < 2 ^ 5) (hl6 : ∀ a ∈ masks4 6, a < 2 ^ 6)
    (hf5 : ∀ α ∈ fours 5, ∃ a ∈ masks4 5, dec 5 a = α)
    (hf6 : ∀ α ∈ fours 6, ∃ a ∈ masks4 6, dec 6 a = α) : check () = true := by
  unfold check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨reach_eq_of hs5 h5 hl5 hf5, reach_eq_of hs6 h6 hl6 hf6⟩

end CFSG.KC.AEOrbitK
