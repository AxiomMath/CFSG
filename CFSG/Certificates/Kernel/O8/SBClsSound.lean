module

public import Certificates.Data.Kernel.O8.SBCls

public section

namespace CFSG.KC.SBCls

open CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem strictT_eq {α : Type} (y : ℕ) (k : ℕ → α) : strictT y k = k y := by cases y <;> rfl

variable (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ)

@[expose] def recAdd (o w : ℕ) (acc : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) (g : ℕ) :
    List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ :=
  if acc.2.2.testBit (cconj mul inv g o) then acc
  else ((cconj mul inv g o, mul g w) :: acc.1, acc.2.1 ++ [(cconj mul inv g o, mul g w)],
    acc.2.2 ||| 2 ^ cconj mul inv g o)

theorem recMStep_cons (o w : ℕ) (q R : List (ℕ × ℕ)) (M : ℕ) :
    recMStep mul inv gens (R, (o, w) :: q, M) = gens.foldl (recAdd mul inv o w) (R, q, M) := rfl

theorem bfsAdd_eq (o w : ℕ) (acc : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) (g : ℕ) :
    bfsAdd mul inv o w acc g =
      if acc.2.2.testBit (cconj mul inv g o) then acc
      else ((cconj mul inv g o, mul g w) :: acc.1, (cconj mul inv g o, mul g w) :: acc.2.1,
        acc.2.2 ||| 2 ^ cconj mul inv g o) := by
  simp only [bfsAdd, strictT_eq]

@[expose] def absQ (st : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) :
    List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ :=
  (st.1, st.2.1 ++ st.2.2.1.reverse, st.2.2.2)

theorem foldl_sim (o w : ℕ) (Q0 : List (ℕ × ℕ)) :
    ∀ (L : List ℕ) (R B : List (ℕ × ℕ)) (M : ℕ),
      L.foldl (recAdd mul inv o w) (R, Q0 ++ B.reverse, M) =
        (fun a => (a.1, Q0 ++ a.2.1.reverse, a.2.2)) (L.foldl (bfsAdd mul inv o w) (R, B, M))
  | [], _, _, _ => rfl
  | g :: L, R, B, M => by
    rw [List.foldl_cons, List.foldl_cons, bfsAdd_eq]
    by_cases h : M.testBit (cconj mul inv g o) = true
    · simp only [recAdd, h, if_true]
      exact foldl_sim o w Q0 L R B M
    · simp only [recAdd, h, Bool.false_eq_true, if_false]
      have e := foldl_sim o w Q0 L ((cconj mul inv g o, mul g w) :: R)
        ((cconj mul inv g o, mul g w) :: B) (M ||| 2 ^ cconj mul inv g o)
      rw [List.reverse_cons, ← List.append_assoc] at e
      exact e

theorem step_sim (st : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) :
    recMStep mul inv gens (absQ st) = absQ (bfsStep mul inv gens st) := by
  obtain ⟨R, F, B, M⟩ := st
  cases F with
  | cons p q =>
    obtain ⟨o, w⟩ := p
    change recMStep mul inv gens (R, (o, w) :: (q ++ B.reverse), M) =
      absQ (bfsPop mul inv gens o w q (R, B, M))
    rw [recMStep_cons, foldl_sim]
    rfl
  | nil =>
    cases hB : B.reverse with
    | nil =>
      have : B = [] := List.reverse_eq_nil_iff.1 hB
      subst this
      rfl
    | cons p q =>
      obtain ⟨o, w⟩ := p
      have e1 : absQ (R, [], B, M) = (R, (o, w) :: (q ++ ([] : List (ℕ × ℕ)).reverse), M) := by
        simp [absQ, hB]
      have e2 : bfsStep mul inv gens (R, [], B, M) = bfsPop mul inv gens o w q (R, [], M) := by
        simp only [bfsStep, hB]
      rw [e1, e2, recMStep_cons, foldl_sim]
      rfl

theorem run_sim : ∀ (L : List ℕ) (st : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ),
    L.foldl (fun st _ => recMStep mul inv gens st) (absQ st) =
      absQ (L.foldl (fun st _ => bfsStep mul inv gens st) st)
  | [], _ => rfl
  | _ :: L, st => by
    rw [List.foldl_cons, List.foldl_cons, step_sim]
    exact run_sim L _

theorem recM_gen (L : List ℕ) (u : ℕ) :
    (L.foldl (fun st _ => recMStep mul inv gens st) ([(u, 0)], [(u, 0)], 2 ^ u)).1 =
      (L.foldl (fun st _ => bfsStep mul inv gens st) ([(u, 0)], [(u, 0)], [], 2 ^ u)).1 := by
  have := congrArg Prod.fst (run_sim mul inv gens L ([(u, 0)], [(u, 0)], [], 2 ^ u))
  simpa only [absQ, List.reverse_nil, List.append_nil] using this

theorem recM_eq (u : ℕ) : recM mul inv gens u = (bfsRun mul inv gens u).1 := by
  unfold recM bfsRun
  exact recM_gen mul inv gens _ u

@[expose] def Tracks (M : ℕ) (R : List (ℕ × ℕ)) : Prop :=
  ∀ x, M.testBit x = true ↔ x ∈ R.map Prod.fst

@[expose] def AddPost (o : ℕ) (L : List ℕ) (R B : List (ℕ × ℕ))
    (a : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) : Prop :=
  Tracks a.2.2 a.1 ∧ (∀ x ∈ R.map Prod.fst, x ∈ a.1.map Prod.fst) ∧
    (∀ x ∈ B.map Prod.fst, x ∈ a.2.1.map Prod.fst) ∧
    (∀ g ∈ L, cconj mul inv g o ∈ a.1.map Prod.fst) ∧
    ∀ x ∈ a.1.map Prod.fst, x ∈ R.map Prod.fst ∨ x ∈ a.2.1.map Prod.fst

theorem foldl_add_post (o w : ℕ) : ∀ (L : List ℕ) (R B : List (ℕ × ℕ)) (M : ℕ), Tracks M R →
    AddPost mul inv o L R B (L.foldl (bfsAdd mul inv o w) (R, B, M))
  | [], R, B, M, hM => ⟨hM, fun _ h => h, fun _ h => h, fun _ h => by simp at h,
      fun _ h => Or.inl h⟩
  | g :: L, R, B, M, hM => by
    rw [List.foldl_cons, bfsAdd_eq]
    by_cases h : M.testBit (cconj mul inv g o) = true
    · simp only [h, if_true]
      obtain ⟨h1, h2, h3, h4, h5⟩ := foldl_add_post o w L R B M hM
      refine ⟨h1, h2, h3, fun g' hg' => ?_, h5⟩
      rcases List.mem_cons.1 hg' with rfl | hg'
      · exact h2 _ ((hM _).1 h)
      · exact h4 g' hg'
    · simp only [h, Bool.false_eq_true, if_false]
      have hM' : Tracks (M ||| 2 ^ cconj mul inv g o) ((cconj mul inv g o, mul g w) :: R) := by
        intro x
        rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, hM, List.map_cons,
          List.mem_cons, decide_eq_true_eq, eq_comm, or_comm]
      obtain ⟨h1, h2, h3, h4, h5⟩ := foldl_add_post o w L _ _ _ hM'
      refine ⟨h1, fun x hx => h2 x (List.mem_cons_of_mem _ hx),
        fun x hx => h3 x (List.mem_cons_of_mem _ hx), fun g' hg' => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.1 hg' with rfl | hg'
        · exact h2 _ List.mem_cons_self
        · exact h4 g' hg'
      · rcases h5 x hx with hx' | hx'
        · rcases List.mem_cons.1 hx' with rfl | hx'
          · exact Or.inr (h3 _ List.mem_cons_self)
          · exact Or.inl hx'
        · exact Or.inr hx'

@[expose] def BfsInv (u : ℕ) (st : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) : Prop :=
  Tracks st.2.2.2 st.1 ∧
    (∀ x ∈ st.1.map Prod.fst, x ∈ (st.2.1 ++ st.2.2.1).map Prod.fst ∨
      ∀ g ∈ gens, cconj mul inv g x ∈ st.1.map Prod.fst) ∧
    u ∈ st.1.map Prod.fst

theorem bfsPop_inv {u o w : ℕ} {q R B : List (ℕ × ℕ)} {M : ℕ} (hM : Tracks M R)
    (hu : u ∈ R.map Prod.fst)
    (hR : ∀ x ∈ R.map Prod.fst, x = o ∨ x ∈ q.map Prod.fst ∨ x ∈ B.map Prod.fst ∨
      ∀ g ∈ gens, cconj mul inv g x ∈ R.map Prod.fst) :
    BfsInv mul inv gens u (bfsPop mul inv gens o w q (R, B, M)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := foldl_add_post mul inv o w gens R B M hM
  refine ⟨h1, fun x hx => ?_, h2 u hu⟩
  simp only [List.map_append, List.mem_append]
  rcases h5 x hx with hx' | hx'
  · rcases hR x hx' with rfl | hq | hB | hc
    · exact Or.inr h4
    · exact Or.inl (Or.inl hq)
    · exact Or.inl (Or.inr (h3 x hB))
    · exact Or.inr fun g hg => h2 _ (hc g hg)
  · exact Or.inl (Or.inr hx')

theorem bfsStep_inv {u : ℕ} {st : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ}
    (h : BfsInv mul inv gens u st) : BfsInv mul inv gens u (bfsStep mul inv gens st) := by
  obtain ⟨R, F, B, M⟩ := st
  obtain ⟨hM, hR, hu⟩ := h
  cases F with
  | cons p q =>
    obtain ⟨o, w⟩ := p
    refine bfsPop_inv mul inv gens hM hu fun x hx => ?_
    rcases hR x hx with hq | hc
    · simp only [List.cons_append, List.map_cons, List.mem_cons, List.map_append,
        List.mem_append] at hq
      rcases hq with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr hc))
  | nil =>
    cases hB : B.reverse with
    | nil =>
      have e : bfsStep mul inv gens (R, [], B, M) = (R, [], B, M) := by
        simp only [bfsStep, hB]
      rw [e]
      exact ⟨hM, hR, hu⟩
    | cons p q =>
      obtain ⟨o, w⟩ := p
      have e : bfsStep mul inv gens (R, [], B, M) = bfsPop mul inv gens o w q (R, [], M) := by
        simp only [bfsStep, hB]
      rw [e]
      refine bfsPop_inv mul inv gens hM hu fun x hx => ?_
      rcases hR x hx with hq | hc
      · have hq' : x ∈ B.reverse.map Prod.fst := by
          simpa only [List.nil_append, List.map_reverse, List.mem_reverse] using hq
        rw [hB, List.map_cons, List.mem_cons] at hq'
        rcases hq' with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr hc))

theorem run_inv {u : ℕ} : ∀ (L : List ℕ) (st : List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ),
    BfsInv mul inv gens u st →
      BfsInv mul inv gens u (L.foldl (fun st _ => bfsStep mul inv gens st) st)
  | [], _, h => h
  | _ :: L, _, h => by
    rw [List.foldl_cons]
    exact run_inv L _ (bfsStep_inv mul inv gens h)

theorem bfsRun_inv (u : ℕ) : BfsInv mul inv gens u (bfsRun mul inv gens u) := by
  refine run_inv mul inv gens _ _ ⟨fun x => ?_, fun x hx => ?_, by simp⟩
  · rw [Nat.testBit_two_pow, decide_eq_true_eq]
    simp [eq_comm]
  · left
    simpa using hx

theorem orbClosedM_of_run {u : ℕ} (hF : (bfsRun mul inv gens u).2.1.isEmpty = true)
    (hB : (bfsRun mul inv gens u).2.2.1.isEmpty = true) :
    orbClosedM mul inv gens u (bfsRun mul inv gens u).1 = true := by
  obtain ⟨-, hR, hu⟩ := bfsRun_inv mul inv gens u
  rw [List.isEmpty_iff] at hF hB
  rw [hF, hB] at hR
  unfold orbClosedM
  simp only [Bool.and_eq_true, List.all_eq_true, testBit_maskOf]
  refine ⟨hu, fun p hp g hg => ?_⟩
  rcases hR p.1 (List.mem_map_of_mem hp) with h | h
  · simp at h
  · exact h g hg

theorem clsChk_imp {N : ℕ} {r : ℕ × ℕ} (h : clsChk mul inv gens N r = true) :
    (decide (r.1 < N) && mul r.1 r.1 == 0 && r.1 != 0 &&
      orbOKM mul inv N r.1 (recM mul inv gens r.1) &&
      orbClosedM mul inv gens r.1 (recM mul inv gens r.1) &&
      (recM mul inv gens r.1).length == r.2 &&
      (recM mul inv gens r.1).all fun p => decide (r.1 ≤ p.1)) = true := by
  rw [recM_eq]
  unfold clsChk at h
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hF⟩, hB⟩, hl⟩, ha⟩, hok⟩ := h
  exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hok⟩, orbClosedM_of_run mul inv gens hF hB⟩, hl⟩, ha⟩

end CFSG.KC.SBCls

end
