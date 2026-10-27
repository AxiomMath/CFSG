module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Digits.Defs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

section HashClosure

variable {X : Type*} [Group X] {E : Type*} [BEq E] [Hashable E]

@[expose] def layerH (nrm : X → X) (enc : X → E) (gens : List X) (seen : Std.HashSet E)
    (frontier : List X) : List X × Std.HashSet E :=
  frontier.foldl (fun (p : List X × Std.HashSet E) x =>
    gens.foldl (fun (q : List X × Std.HashSet E) g =>
      if q.2.contains (enc (nrm (g * x))) then q
      else (nrm (g * x) :: q.1, q.2.insert (enc (nrm (g * x))))) p) ([], seen)

@[expose] def closureH (nrm : X → X) (enc : X → E) (gens : List X) :
    ℕ → List X → Std.HashSet E → List X → List X
  | 0, all, _, _ => all
  | f + 1, all, seen, frontier =>
    let r := layerH nrm enc gens seen frontier
    if r.1.isEmpty then all else closureH nrm enc gens f (all ++ r.1.reverse) r.2 r.1.reverse

@[expose] def closureListH (nrm : X → X) (enc : X → E) (gens : List X) (fuel : ℕ) : List X :=
  closureH nrm enc gens fuel [1] ((∅ : Std.HashSet E).insert (enc 1)) [1]

omit [BEq E] [Hashable E] in
theorem layerH_subset (nrm : X → X) (hnrm : ∀ x, nrm x = x) (enc : X → E) [BEq E] [Hashable E]
    (gens : List X) (seen : Std.HashSet E) (frontier : List X) :
    ∀ y ∈ (layerH nrm enc gens seen frontier).1, ∃ x ∈ frontier, ∃ g ∈ gens, y = g * x := by
  have key : ∀ (fr : List X) (p : List X × Std.HashSet E), (∀ y ∈ p.1, ∃ x ∈ frontier,
      ∃ g ∈ gens, y = g * x) → (∀ x ∈ fr, x ∈ frontier) →
      ∀ y ∈ (fr.foldl (fun (p : List X × Std.HashSet E) x =>
        gens.foldl (fun (q : List X × Std.HashSet E) g =>
          if q.2.contains (enc (nrm (g * x))) then q
          else (nrm (g * x) :: q.1, q.2.insert (enc (nrm (g * x))))) p) p).1,
        ∃ x ∈ frontier, ∃ g ∈ gens, y = g * x := by
    intro fr
    induction fr with
    | nil => intro p hp _ y hy; exact hp y hy
    | cons x fr ih =>
      intro p hp hfr
      simp only [List.foldl_cons]
      refine ih _ ?_ (fun x' hx' => hfr x' (List.mem_cons_of_mem _ hx'))
      have hx : x ∈ frontier := hfr x List.mem_cons_self
      have inner : ∀ (gl : List X), (∀ g ∈ gl, g ∈ gens) → ∀ (q : List X × Std.HashSet E),
          (∀ y ∈ q.1, ∃ x ∈ frontier, ∃ g ∈ gens, y = g * x) →
          ∀ y ∈ (gl.foldl (fun (q : List X × Std.HashSet E) g =>
            if q.2.contains (enc (nrm (g * x))) then q
            else (nrm (g * x) :: q.1, q.2.insert (enc (nrm (g * x))))) q).1,
            ∃ x ∈ frontier, ∃ g ∈ gens, y = g * x := by
        intro gl
        induction gl with
        | nil => intro _ q hq y hy; exact hq y hy
        | cons g gl ih2 =>
          intro hgl q hq
          simp only [List.foldl_cons]
          refine ih2 (fun g' hg' => hgl g' (List.mem_cons_of_mem _ hg')) _ ?_
          split_ifs with h
          · exact hq
          · intro y hy
            rcases List.mem_cons.1 hy with rfl | hy
            · exact ⟨x, hx, g, hgl g List.mem_cons_self, hnrm _⟩
            · exact hq y hy
      exact inner gens (fun g hg => hg) p hp
  intro y hy
  exact key frontier ([], seen) (fun y hy => by simp at hy) (fun x hx => hx) y hy

omit [BEq E] [Hashable E] in
theorem closureH_subset (nrm : X → X) (hnrm : ∀ x, nrm x = x) (enc : X → E) [BEq E] [Hashable E]
    (gens : List X) :
    ∀ (fuel : ℕ) (all : List X) (seen : Std.HashSet E) (frontier : List X),
      (∀ y ∈ all, y ∈ Subgroup.closure {g | g ∈ gens}) →
      (∀ y ∈ frontier, y ∈ Subgroup.closure {g | g ∈ gens}) →
      ∀ y ∈ closureH nrm enc gens fuel all seen frontier,
        y ∈ Subgroup.closure {g | g ∈ gens} := by
  intro fuel
  induction fuel with
  | zero => intro all seen frontier hall _ y hy; exact hall y hy
  | succ f ih =>
    intro all seen frontier hall hfr y hy
    simp only [closureH] at hy
    split_ifs at hy with h
    · exact hall y hy
    · refine ih _ _ _ ?_ ?_ y hy
      · intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · exact hall z hz
        · obtain ⟨x, hx, g, hg, rfl⟩ := layerH_subset nrm hnrm enc gens seen frontier z
            (List.mem_reverse.1 hz)
          exact Subgroup.mul_mem _ (Subgroup.subset_closure hg) (hfr x hx)
      · intro z hz
        obtain ⟨x, hx, g, hg, rfl⟩ := layerH_subset nrm hnrm enc gens seen frontier z
          (List.mem_reverse.1 hz)
        exact Subgroup.mul_mem _ (Subgroup.subset_closure hg) (hfr x hx)

omit [BEq E] [Hashable E] in
theorem closureListH_subset (nrm : X → X) (hnrm : ∀ x, nrm x = x) (enc : X → E) [BEq E]
    [Hashable E] (gens : List X) (fuel : ℕ) :
    ∀ y ∈ closureListH nrm enc gens fuel, y ∈ Subgroup.closure {g | g ∈ gens} := by
  intro y hy
  refine closureH_subset nrm hnrm enc gens fuel [1] _ [1] ?_ ?_ y hy
  · intro z hz
    simp only [List.mem_singleton] at hz
    rw [hz]
    exact Subgroup.one_mem _
  · intro z hz
    simp only [List.mem_singleton] at hz
    rw [hz]
    exact Subgroup.one_mem _

end HashClosure

section Closure

variable {X : Type*} [Group X] {E : Type*} [DecidableEq E]

@[expose] def dedupBy (enc : X → E) (l : List X) : List X :=
  (l.foldl (fun (p : List X × List E) y => if enc y ∈ p.2 then p else (y :: p.1, enc y :: p.2))
    ([], [])).1.reverse

omit [Group X] in
theorem mem_dedupBy {enc : X → E} {l : List X} {y : X} (h : y ∈ dedupBy enc l) : y ∈ l := by
  have key : ∀ (l : List X) (p : List X × List E), y ∈ (l.foldl (fun (p : List X × List E) y =>
      if enc y ∈ p.2 then p else (y :: p.1, enc y :: p.2)) p).1 → y ∈ p.1 ∨ y ∈ l := by
    intro l
    induction l with
    | nil => intro p hp; exact Or.inl hp
    | cons z l ih =>
      intro p hp
      simp only [List.foldl_cons] at hp
      split_ifs at hp with hz
      · rcases ih p hp with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases ih _ hp with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
  have h' : y ∈ (l.foldl (fun (p : List X × List E) y =>
      if enc y ∈ p.2 then p else (y :: p.1, enc y :: p.2)) ([], [])).1 := by
    simpa [dedupBy] using h
  rcases key l ([], []) h' with h | h
  · simp at h
  · exact h

@[expose] def closureStep (nrm : X → X) (enc : X → E) (gens L : List X) : List X :=
  let EL := L.map enc
  L ++ dedupBy enc ((L.flatMap fun x => gens.map fun g => nrm (g * x)).filter
    fun y => decide (enc y ∉ EL))

@[expose] def closureList (nrm : X → X) (enc : X → E) (gens : List X) : ℕ → List X
  | 0 => [1]
  | k + 1 => closureStep nrm enc gens (closureList nrm enc gens k)

theorem closureList_subset_closure (nrm : X → X) (hnrm : ∀ x, nrm x = x) (enc : X → E)
    (gens : List X) :
    ∀ k, ∀ x ∈ closureList nrm enc gens k, x ∈ Subgroup.closure {g | g ∈ gens} := by
  intro k
  induction k with
  | zero =>
    intro x hx
    simp only [closureList, List.mem_singleton] at hx
    rw [hx]
    exact Subgroup.one_mem _
  | succ k ih =>
    intro x hx
    simp only [closureList, closureStep, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ih x hx
    · have hx' := mem_dedupBy hx
      simp only [List.mem_filter, List.mem_flatMap, List.mem_map] at hx'
      obtain ⟨⟨y, hy, g, hg, rfl⟩, -⟩ := hx'
      rw [hnrm]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure hg) (ih y hy)

@[expose] def nrmTestGens (enc : X → E) (EA : List E) (gens : List X) (g : X) : Bool :=
  gens.all fun a => decide (enc (g * a * g⁻¹) ∈ EA)

end Closure

section Nodup

@[expose] def strictAsc : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a < b) && strictAsc (b :: l)

theorem strictAsc_pairwise : ∀ {l : List ℕ}, strictAsc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictAsc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := strictAsc_pairwise h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 ((List.pairwise_cons.1 ih).1 x hx)

theorem nodup_of_strictAsc {α : Type*} (f : α → ℕ) (L : List α)
    (h : strictAsc ((L.map f).mergeSort (fun a b => decide (a ≤ b))) = true) : L.Nodup := by
  have hp := strictAsc_pairwise h
  have hnd : ((L.map f).mergeSort (fun a b => decide (a ≤ b))).Nodup :=
    hp.imp (fun h => ne_of_lt h)
  have hperm := List.mergeSort_perm (L.map f) (fun a b => decide (a ≤ b))
  have : (L.map f).Nodup := hperm.nodup_iff.1 hnd
  exact List.Nodup.of_map f this

end Nodup

section Subgroups

variable {X : Type*} [Group X] [Finite X]

theorem subgroupOfGens_exists (rg Rl : List X) (hRl : ∀ x ∈ Rl, x ∈ Subgroup.closure {g | g ∈ rg})
    (h1 : (1 : X) ∈ Rl) (hgen : ∀ x ∈ Rl, ∀ g ∈ rg, x * g ∈ Rl) :
    ∀ x, x ∈ Subgroup.closure {g | g ∈ rg} ↔ x ∈ Rl := by
  intro x
  refine ⟨fun hx => ?_, hRl x⟩
  have key : ∀ x ∈ Subgroup.closure {g | g ∈ rg}, ∀ y ∈ Rl, y * x ∈ Rl := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem g hg => exact fun y hy => hgen y hy g hg
    | one => exact fun y hy => by simpa using hy
    | mul a b _ _ ha hb => exact fun y hy => by rw [← mul_assoc]; exact hb _ (ha y hy)
    | inv a _ ha =>
      intro y hy
      have hpow : ∀ n : ℕ, y * a ^ n ∈ Rl := by
        intro n
        induction n with
        | zero => simpa using hy
        | succ n ih => rw [pow_succ, ← mul_assoc]; exact ha _ ih
      have hpos := orderOf_pos a
      have : a⁻¹ = a ^ (orderOf a - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv', ← pow_succ', Nat.sub_add_cancel hpos,
          pow_orderOf_eq_one]
      rw [this]
      exact hpow _
  simpa using key x hx 1 h1

end Subgroups

section EncPerm

@[expose] def encPerm {n : ℕ} (g : Equiv.Perm (Fin n)) : ℕ :=
  Nat.ofDigits n ((List.finRange n).map fun i => (g i).val)

theorem encPerm_injective {n : ℕ} (hn : 1 < n) : Function.Injective (encPerm (n := n)) := by
  intro g h hgh
  have hdig : ∀ k : Equiv.Perm (Fin n), ∀ l ∈ (List.finRange n).map (fun i => (k i).val),
      l < n := by
    intro k l hl
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
    exact (k i).isLt
  have hl := Nat.ofDigits_inj_of_len_eq hn (by simp) (hdig g) (hdig h) hgh
  refine Equiv.ext fun i => Fin.ext ?_
  have := congrArg (fun l : List ℕ => l[i.val]?) hl
  simpa using this

end EncPerm

section Card

theorem mem_list_of_card_le {X : Type*} (U : Set X) [Finite U] (L : List X) (hL : L.Nodup)
    (hsub : ∀ x ∈ L, x ∈ U) (hcard : Nat.card U ≤ L.length) : ∀ x ∈ U, x ∈ L := by
  classical
  have hsub' : (↑L.toFinset : Set X) ⊆ U := by
    intro x hx
    exact hsub x (List.mem_toFinset.1 hx)
  have hn : (↑L.toFinset : Set X).ncard = L.length := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]
  have heq := Set.eq_of_subset_of_ncard_le hsub' (by rw [hn, ← Nat.card_coe_set_eq]; exact hcard)
    (Set.toFinite U)
  intro x hx
  have : x ∈ (↑L.toFinset : Set X) := heq ▸ hx
  exact List.mem_toFinset.1 this

end Card

end CFSG.QuasithinUnique.Vol2Native.L239
