module

public import CFSG.Certificates.Kernel.LocalQTPermWSnd.Gen

public section

namespace CFSG.KC.LQT.PWSnd

@[expose] def bfsT {Ω Γ : Type*} (op : Ω → Γ → Ω) (d : Γ) (gens : List Γ) (start : Ω)
    (par : List (ℕ × ℕ)) : List Ω :=
  par.foldl (fun acc pk => acc ++ [op (acc.getD pk.1 start) (gens.getD pk.2 d)]) [start]

private theorem foldl_length_bfsT {Ω Γ : Type*} (op : Ω → Γ → Ω) (d : Γ) (gens : List Γ)
    (start : Ω) : ∀ (par : List (ℕ × ℕ)) (acc : List Ω),
      (par.foldl (fun (b : List Ω) (p : ℕ × ℕ) => b ++ [op (b.getD p.1 start) (gens.getD p.2 d)])
        acc).length = acc.length + par.length
  | [], _ => by simp
  | pk :: par, acc => by
    rw [List.foldl_cons, foldl_length_bfsT op d gens start par, List.length_append,
      List.length_singleton, List.length_cons]
    omega

private theorem mem_foldl_bfsT {Ω Γ : Type*} (op : Ω → Γ → Ω) (d : Γ) (gens : List Γ)
    (start : Ω) : ∀ (par : List (ℕ × ℕ)) (acc : List Ω) (a : Ω), a ∈ acc →
      a ∈ par.foldl (fun (b : List Ω) (p : ℕ × ℕ) => b ++ [op (b.getD p.1 start) (gens.getD p.2 d)])
        acc
  | [], _, _, ha => ha
  | pk :: par, acc, a, ha => by
    rw [List.foldl_cons]
    exact mem_foldl_bfsT op d gens start par (acc ++ [op (acc.getD pk.1 start) (gens.getD pk.2 d)])
      a (List.mem_append.mpr (Or.inl ha))

private theorem foldl_map_bfsT {Ω Γ : Type*} (f : Ω → ℕ) (c : Γ → ℕ) (op : Ω → Γ → Ω)
    (opN : ℕ → ℕ → ℕ) (hop : ∀ x g, f (op x g) = opN (f x) (c g)) (d : Γ) (dN : ℕ)
    (gens : List Γ) (start : Ω) : ∀ (par : List (ℕ × ℕ)),
      (∀ q ∈ par, (gens.map c).getD q.2 dN = c (gens.getD q.2 d)) → ∀ (acc : List Ω),
      (par.foldl (fun (b : List Ω) (p : ℕ × ℕ) => b ++ [op (b.getD p.1 start) (gens.getD p.2 d)])
          acc).map f =
        par.foldl (fun (b : List ℕ) (p : ℕ × ℕ) =>
          b ++ [opN (b.getD p.1 (f start)) ((gens.map c).getD p.2 dN)]) (acc.map f)
  | [], _, _ => rfl
  | pk :: par, hdef, acc => by
    have hdef' : ∀ q ∈ par, (gens.map c).getD q.2 dN = c (gens.getD q.2 d) :=
      fun q hq => hdef q (List.mem_cons_of_mem _ hq)
    have hpk : (gens.map c).getD pk.2 dN = c (gens.getD pk.2 d) := hdef pk (by simp)
    rw [List.foldl_cons, List.foldl_cons, foldl_map_bfsT f c op opN hop d dN gens start par hdef',
      List.map_append, List.map_singleton, hop, List.getD_map, hpk]

private theorem getD_mem_of {α : Type*} (l : List α) (d : α) (S : Set α) (hd : d ∈ S)
    (hl : ∀ a ∈ l, a ∈ S) (n : ℕ) : l.getD n d ∈ S := by
  rcases Nat.lt_or_ge n l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hl _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    exact hd

private theorem getD_one_mem_or {Γ : Type*} [One Γ] (gens : List Γ) (s : ℕ) :
    gens.getD s 1 ∈ gens ∨ gens.getD s 1 = 1 := by
  rcases Nat.lt_or_ge s gens.length with h | h
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ h

private theorem getD_append_single_ne {α : Type*} (l : List α) (v d : α) (i : ℕ)
    (hi : i ≠ l.length) : (l ++ [v]).getD i d = l.getD i d := by
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · have h' : (l ++ [v]).length ≤ i := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [List.getD_eq_default _ _ h', List.getD_eq_default _ _ h]

private theorem getD_append_length_single {α : Type*} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp [List.getElem?_concat_length]

theorem length_bfsT {Ω Γ : Type*} (op : Ω → Γ → Ω) (d : Γ) (gens : List Γ) (start : Ω)
    (par : List (ℕ × ℕ)) : (bfsT op d gens start par).length = par.length + 1 := by
  have h := foldl_length_bfsT op d gens start par [start]
  rw [List.length_singleton] at h
  unfold bfsT
  rw [h]
  omega

theorem start_mem_bfsT {Ω Γ : Type*} (op : Ω → Γ → Ω) (d : Γ) (gens : List Γ) (start : Ω)
    (par : List (ℕ × ℕ)) : start ∈ bfsT op d gens start par := by
  unfold bfsT
  exact mem_foldl_bfsT op d gens start par [start] start (by simp)

theorem bfsT_map {Ω Γ : Type*} (f : Ω → ℕ) (c : Γ → ℕ) (op : Ω → Γ → Ω) (opN : ℕ → ℕ → ℕ)
    (hop : ∀ x g, f (op x g) = opN (f x) (c g)) (d : Γ) (dN : ℕ) (gens : List Γ) (start : Ω)
    (par : List (ℕ × ℕ)) (hdef : ∀ q ∈ par, (gens.map c).getD q.2 dN = c (gens.getD q.2 d)) :
    (bfsT op d gens start par).map f = bfsT opN dN (gens.map c) (f start) par := by
  exact foldl_map_bfsT f c op opN hop d dN gens start par hdef [start]

private theorem mul_getD_mem_ball {X : Type*} [Group X] (gens : List X) (s : ℕ) (x : X) (k : ℕ)
    (hx : x ∈ Ball gens k) : gens.getD s 1 * x ∈ Ball gens (k + 1) := by
  rcases getD_one_mem_or gens s with hg | hg
  · exact mul_mem_ball gens hg hx
  · rw [hg, one_mul]
    exact ball_mono gens (Nat.le_succ k) hx

private theorem foldl_ball {X : Type*} [Group X] (gens : List X) :
    ∀ (par : List (ℕ × ℕ)) (acc : List X) (accD : List ℕ), acc.length = accD.length →
      (∀ j, acc.getD j 1 ∈ Ball gens (accD.getD j 0)) →
      ∀ i, (par.foldl (fun (b : List X) (p : ℕ × ℕ) => b ++ [gens.getD p.2 1 * b.getD p.1 1])
          acc).getD i 1 ∈
        Ball gens ((par.foldl (fun (b : List ℕ) (p : ℕ × ℕ) => b ++ [b.getD p.1 0 + 1])
          accD).getD i 0)
  | [], _, _, _, hI, i => hI i
  | pk :: par, acc, accD, hlen, hI, i => by
    rw [List.foldl_cons, List.foldl_cons]
    refine foldl_ball gens par (acc ++ [gens.getD pk.2 1 * acc.getD pk.1 1])
      (accD ++ [accD.getD pk.1 0 + 1]) ?_ ?_ i
    · simp only [List.length_append, List.length_singleton, hlen]
    · intro j
      by_cases hj : j = acc.length
      · subst hj
        have e1 : (acc ++ [gens.getD pk.2 1 * acc.getD pk.1 1]).getD acc.length 1 =
            gens.getD pk.2 1 * acc.getD pk.1 1 := getD_append_length_single acc _ 1
        have e2 : (accD ++ [accD.getD pk.1 0 + 1]).getD acc.length 0 =
            accD.getD pk.1 0 + 1 := by
          rw [hlen]
          exact getD_append_length_single accD _ 0
        rw [e1, e2]
        exact mul_getD_mem_ball gens pk.2 (acc.getD pk.1 1) (accD.getD pk.1 0) (hI pk.1)
      · have hj' : j ≠ accD.length := by
          rw [← hlen]
          exact hj
        rw [getD_append_single_ne acc _ 1 j hj, getD_append_single_ne accD _ 0 j hj']
        exact hI j

theorem bfsT_ball {X : Type*} [Group X] (gens : List X) {Γ' : Type*} (gens' : List Γ') (d' : Γ')
    (par : List (ℕ × ℕ)) (i : ℕ) :
    (bfsT (fun (x g : X) => g * x) 1 gens 1 par).getD i 1 ∈
      Ball gens ((bfsT (fun (n : ℕ) (_ : Γ') => n + 1) d' gens' 0 par).getD i 0) := by
  refine foldl_ball gens par [1] [0] rfl ?_ i
  intro j
  rcases j with _ | j <;> simpa using one_mem_ball gens 0

theorem bfsT_subset_ball {X : Type*} [Group X] (gens : List X) {Γ' : Type*} (gens' : List Γ')
    (d' : Γ') (par : List (ℕ × ℕ)) (fuel : ℕ)
    (hD : ∀ k ∈ bfsT (fun (n : ℕ) (_ : Γ') => n + 1) d' gens' 0 par, k ≤ fuel) :
    ∀ y ∈ bfsT (fun (x g : X) => g * x) 1 gens 1 par, y ∈ Ball gens fuel := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
  have hlenD := length_bfsT (fun (n : ℕ) (_ : Γ') => n + 1) d' gens' 0 par
  have hlenT := length_bfsT (fun (x g : X) => g * x) 1 gens 1 par
  have hDlen : i < (bfsT (fun (n : ℕ) (_ : Γ') => n + 1) d' gens' 0 par).length := by
    rw [hlenD]
    rw [hlenT] at hi
    exact hi
  have hmem : (bfsT (fun (n : ℕ) (_ : Γ') => n + 1) d' gens' 0 par).getD i 0 ∈
      bfsT (fun (n : ℕ) (_ : Γ') => n + 1) d' gens' 0 par := by
    rw [List.getD_eq_getElem _ _ hDlen]
    exact List.getElem_mem hDlen
  have hb := bfsT_ball gens gens' d' par i
  rw [List.getD_eq_getElem _ _ hi] at hb
  exact ball_mono gens (hD _ hmem) hb

private theorem foldl_reach {Γ Ω : Type*} [Group Γ] [MulAction Γ Ω] (gens : List Γ) (x₀ : Ω)
    (S : Set Ω) (h0 : x₀ ∈ S) (hS : ∀ g ∈ gens, ∀ x ∈ S, g • x ∈ S) :
    ∀ (par : List (ℕ × ℕ)) (acc : List Ω), (∀ a ∈ acc, a ∈ S) →
      ∀ y ∈ par.foldl (fun (b : List Ω) (p : ℕ × ℕ) => b ++ [gens.getD p.2 1 • b.getD p.1 x₀]) acc,
        y ∈ S
  | [], _, hacc, y, hy => hacc y hy
  | pk :: par, acc, hacc, y, hy => by
    rw [List.foldl_cons] at hy
    refine foldl_reach gens x₀ S h0 hS par (acc ++ [gens.getD pk.2 1 • acc.getD pk.1 x₀]) ?_ y hy
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hacc a h
    · rcases List.mem_singleton.mp h with rfl
      have hx : acc.getD pk.1 x₀ ∈ S := getD_mem_of acc x₀ S h0 hacc pk.1
      rcases getD_one_mem_or gens pk.2 with hg | hg
      · exact hS _ hg _ hx
      · rw [hg, one_smul]
        exact hx

theorem bfsT_reach {Γ Ω : Type*} [Group Γ] [MulAction Γ Ω] (gens : List Γ) (x₀ : Ω)
    (par : List (ℕ × ℕ)) (S : Set Ω) (h0 : x₀ ∈ S) (hS : ∀ g ∈ gens, ∀ x ∈ S, g • x ∈ S) :
    ∀ y ∈ bfsT (fun (x : Ω) (g : Γ) => g • x) 1 gens x₀ par, y ∈ S := by
  have hacc : ∀ a ∈ [x₀], a ∈ S := by
    intro a ha
    rcases List.mem_singleton.mp ha with rfl
    exact h0
  exact foldl_reach gens x₀ S h0 hS par [x₀] hacc

end CFSG.KC.LQT.PWSnd

end
