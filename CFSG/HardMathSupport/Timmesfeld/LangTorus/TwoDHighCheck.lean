module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.HardMathSupport.Timmesfeld.RootAut TauCeti

variable {n : ℕ}

@[expose] def sepPairB (M : Matrix (Fin n) (Fin n) ℤ) (K : ℕ) (a b : Fin n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide (i = j) || (decide (i = a ∨ i = b) && decide (j = a ∨ j = b)) ||
      (List.range K).any fun k =>
        (walkList M k).getD i 0 != (walkList M k).getD j 0 ||
          (walkList M.transpose k).getD i 0 != (walkList M.transpose k).getD j 0

theorem apply_eq_self_of_sepPairB {M : Matrix (Fin n) (Fin n) ℤ} {K : ℕ} {a b : Fin n}
    (h : sepPairB M K a b = true) {σ : Equiv.Perm (Fin n)} (hσ : ∀ i j, M (σ i) (σ j) = M i j)
    {i : Fin n} (hia : i ≠ a) (hib : i ≠ b) : σ i = i := by
  have hσT : ∀ i j, M.transpose (σ i) (σ j) = M.transpose i j := fun i j => hσ j i
  by_contra hne
  simp only [sepPairB, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, bne_iff_ne] at h
  rcases h (σ i) i with (h1 | ⟨-, h1⟩) | ⟨k, -, h2 | h2⟩
  · exact hne h1
  · rcases h1 with h1 | h1
    · exact hia h1
    · exact hib h1
  · exact h2 (walkList_perm hσ k i)
  · exact h2 (walkList_perm hσT k i)

theorem eq_one_or_eq_swap_of_sepPairB {M : Matrix (Fin n) (Fin n) ℤ} {K : ℕ} {a b : Fin n}
    (h : sepPairB M K a b = true) (hab : a ≠ b) {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j, M (σ i) (σ j) = M i j) : σ = 1 ∨ σ = Equiv.swap a b := by
  have hfix : ∀ i, i ≠ a → i ≠ b → σ i = i := fun i hia hib =>
    apply_eq_self_of_sepPairB h hσ hia hib
  have hmem : ∀ c, (c = a ∨ c = b) → (σ c = a ∨ σ c = b) := by
    intro c hc
    by_contra hcon
    push Not at hcon
    have h1 := hfix (σ c) hcon.1 hcon.2
    have h2 := σ.injective h1
    rw [h2] at hcon
    rcases hc with rfl | rfl
    · exact hcon.1 rfl
    · exact hcon.2 rfl
  rcases hmem a (Or.inl rfl) with ha | ha
  · have hb : σ b = b := by
      rcases hmem b (Or.inr rfl) with hb | hb
      · exact absurd (σ.injective (hb.trans ha.symm)) hab.symm
      · exact hb
    left
    refine Equiv.ext fun i => ?_
    rw [Equiv.Perm.one_apply]
    by_cases hia : i = a
    · rw [hia, ha]
    by_cases hib : i = b
    · rw [hib, hb]
    exact hfix i hia hib
  · have hb : σ b = a := by
      rcases hmem b (Or.inr rfl) with hb | hb
      · exact hb
      · exact absurd (σ.injective (hb.trans ha.symm)) hab.symm
    right
    refine Equiv.ext fun i => ?_
    by_cases hia : i = a
    · rw [hia, ha, Equiv.swap_apply_left]
    by_cases hib : i = b
    · rw [hib, hb, Equiv.swap_apply_right]
    rw [hfix i hia hib, Equiv.swap_apply_of_ne_of_ne hia hib]

@[expose] def swapList (a b : Fin n) (l : List ℤ) : List ℤ :=
  List.ofFn fun i => ofList (n := n) l (Equiv.swap a b i)

@[expose] def formList (M : Matrix (Fin n) (Fin n) ℤ) (l l' : List ℤ) : ℤ :=
  ∑ i, ∑ j, ofList (n := n) l i * M i j * ofList (n := n) l' j

@[expose] def orthOK (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) (L : List (List ℤ)) : Bool :=
  L.all fun l => swapList a b l == l || formList M l (swapList a b l) == 0

theorem swapList_ofFn (a b : Fin n) (x : Fin n → ℤ) :
    swapList a b (List.ofFn x) = List.ofFn (fun i => x (Equiv.swap a b i)) := by
  rw [swapList, ofList_ofFn]

theorem formList_ofFn (M : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) :
    formList M (List.ofFn x) (List.ofFn y) = ∑ i, ∑ j, x i * M i j * y j := by
  rw [formList, ofList_ofFn, ofList_ofFn]

theorem form_swap_eq_zero_of_orthOK {M : Matrix (Fin n) (Fin n) ℤ} {a b : Fin n}
    {L : List (List ℤ)} (h : orthOK M a b L = true) {x : Fin n → ℤ} (hx : List.ofFn x ∈ L)
    (hne : (fun i => x (Equiv.swap a b i)) ≠ x) :
    ∑ i, ∑ j, x i * M i j * x (Equiv.swap a b j) = 0 := by
  simp only [orthOK, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h _ hx with h1 | h1
  · rw [swapList_ofFn] at h1
    exact absurd (List.ofFn_injective h1) hne
  · rw [swapList_ofFn, formList_ofFn] at h1
    exact h1

@[expose] def foldMoves (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) (l : List ℤ) :
    List (List ℤ) :=
  reflectList M a (reflectList M b l) ::
    ((List.finRange n).filter fun i => decide (i ≠ a) && decide (i ≠ b)).map
      fun i => reflectList M i l

@[expose] def foldIter (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) : ℕ → List (List ℤ)
  | 0 => ((List.finRange n).map fun i => List.ofFn (Pi.single i 1 : Fin n → ℤ)).dedup
  | k + 1 => (foldIter M a b k ++ (foldIter M a b k).flatMap (foldMoves M a b)).dedup

inductive IsFoldReach (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) : (Fin n → ℤ) → Prop
  | single (i : Fin n) : IsFoldReach M a b (Pi.single i 1)
  | pair {x : Fin n → ℤ} : IsFoldReach M a b x →
      IsFoldReach M a b (coordReflect M a (coordReflect M b x))
  | one (i : Fin n) {x : Fin n → ℤ} : i ≠ a → i ≠ b → IsFoldReach M a b x →
      IsFoldReach M a b (coordReflect M i x)

theorem mem_foldIter (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) (k : ℕ) {l : List ℤ}
    (hl : l ∈ foldIter M a b k) : ∃ x, IsFoldReach M a b x ∧ l = List.ofFn x := by
  induction k generalizing l with
  | zero =>
    simp only [foldIter, List.mem_dedup, List.mem_map, List.mem_finRange, true_and] at hl
    obtain ⟨i, rfl⟩ := hl
    exact ⟨_, .single i, rfl⟩
  | succ k ih =>
    simp only [foldIter, List.mem_dedup, List.mem_append, List.mem_flatMap] at hl
    rcases hl with hl | ⟨l', hl', hm⟩
    · exact ih hl
    · obtain ⟨x, hx, rfl⟩ := ih hl'
      simp only [foldMoves, List.mem_cons, List.mem_map, List.mem_filter, List.mem_finRange,
        true_and, Bool.and_eq_true, decide_eq_true_eq] at hm
      rcases hm with rfl | ⟨i, ⟨hia, hib⟩, rfl⟩
      · refine ⟨_, .pair hx, ?_⟩
        rw [reflectList_ofFn, reflectList_ofFn]
      · exact ⟨_, .one i hia hib hx, reflectList_ofFn M i x⟩

@[expose] def reachOK (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) (L : List (List ℤ)) (k : ℕ) :
    Bool :=
  L.all fun l => l ∈ foldIter M a b k

theorem isFoldReach_of_reachOK {M : Matrix (Fin n) (Fin n) ℤ} {a b : Fin n}
    {L : List (List ℤ)} {k : ℕ} (h : reachOK M a b L k = true) {x : Fin n → ℤ}
    (hx : List.ofFn x ∈ L) : IsFoldReach M a b x := by
  simp only [reachOK, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨y, hy, e⟩ := mem_foldIter M a b k (h _ hx)
  rw [List.ofFn_injective e]
  exact hy

@[expose] def adjOK (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) : Bool :=
  (List.finRange n).all fun i => decide (i = a ∨ i = b) ||
    (List.finRange n).any fun j => !decide (j = a ∨ j = b) && M i j == -1

theorem exists_adj_of_adjOK {M : Matrix (Fin n) (Fin n) ℤ} {a b : Fin n}
    (h : adjOK M a b = true) {i : Fin n} (hia : i ≠ a) (hib : i ≠ b) :
    ∃ j, j ≠ a ∧ j ≠ b ∧ M i j = -1 := by
  simp only [adjOK, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true, true_and, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, beq_iff_eq] at h
  rcases h i with h1 | ⟨j, hj, hM⟩
  · rcases h1 with h1 | h1
    · exact absurd h1 hia
    · exact absurd h1 hib
  · push Not at hj
    exact ⟨j, hj.1, hj.2, hM⟩

@[expose] def dGraphOK (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) (N : ℕ) : Bool :=
  closedB M (orbitIter M 30) && (orbitIter M 30).length == N && sepPairB M (2 * n) a b &&
    M a b == 0 && orthOK M a b (orbitIter M 30) && reachOK M a b (orbitIter M 30) 30 &&
      adjOK M a b

theorem dGraphOK_spec {M : Matrix (Fin n) (Fin n) ℤ} {a b : Fin n} {N : ℕ}
    (h : dGraphOK M a b N = true) :
    closedB M (orbitIter M 30) = true ∧ (orbitIter M 30).length = N ∧
      sepPairB M (2 * n) a b = true ∧ M a b = 0 ∧ orthOK M a b (orbitIter M 30) = true ∧
      reachOK M a b (orbitIter M 30) 30 = true ∧ adjOK M a b = true := by
  simp only [dGraphOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end CFSG.HardMathSupport.Timmesfeld.LangTorus
