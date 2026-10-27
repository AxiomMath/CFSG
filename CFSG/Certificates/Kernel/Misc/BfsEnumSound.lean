module

public import CFSG.ClassicalInvolution.Solomon73.YamakiEnum

public section

namespace CFSG.KC.BfsEnum

open CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def stepJ (gs : Array (Array ℕ)) (x : Array ℕ) (q : ℕ) (E : Enum) (j : ℕ) : Enum :=
  if (!E.index.contains (compA x gs[j]!)) = true then
    ⟨E.elems.push (compA x gs[j]!), E.parent.push q, E.gen.push j,
      E.index.insert (compA x gs[j]!) E.elems.size⟩
  else E

@[expose] def outerJ (gs : Array (Array ℕ)) (E : Enum) (q : ℕ) : Enum :=
  if q < E.elems.size then bfsStep gs E q else E

@[expose] def initE : Enum :=
  ⟨#[idA ()], #[0], #[0], ({} : Std.HashMap (Array ℕ) ℕ).insert (idA ()) 0⟩

theorem forIn_foldl {β : Type} (l : List ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (g : β → ℕ → β) (h : ∀ j b, f j b = pure (ForInStep.yield (g b j))) :
    Id.run (forIn l init f) = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, h, List.foldl_cons]
    exact ih _

theorem bfsStep_eq (gs : Array (Array ℕ)) (E : Enum) (q : ℕ) :
    bfsStep gs E q = (List.range gs.size).foldl (stepJ gs E.elems[q]! q) E := by
  unfold bfsStep
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.range_eq_range', bind_pure]
  exact forIn_foldl _ _ _ _ fun j b => by unfold stepJ; split <;> rfl

theorem bfsEnum_eq (gs : Array (Array ℕ)) (fuel : ℕ) :
    bfsEnum gs fuel = (List.range fuel).foldl (outerJ gs) initE := by
  unfold bfsEnum
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.range_eq_range', bind_pure]
  exact forIn_foldl _ _ _ _ fun j b => by unfold outerJ; split <;> rfl

@[expose] def BInvE (T : ℕ → Array ℕ) (PA PB : ℕ → ℕ) (c : ℕ) (E : Enum) : Prop :=
  E.elems.size = c ∧ E.parent.size = c ∧ E.gen.size = c ∧ (∀ t < c, E.elems[t]! = T t) ∧
    (∀ t < c, 0 < t → E.parent[t]! = PA (t - 1) ∧ E.gen[t]! = PB (t - 1)) ∧
    (∀ y, E.index.contains y = true ↔ ∃ t < c, T t = y) ∧ (∀ t < c, E.index[T t]? = some t)

theorem push_lt {α : Type} [Inhabited α] {a : Array α} {x : α} {i : ℕ} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), Array.getElem_push_lt h, getElem!_pos a i h]

theorem push_eq {α : Type} [Inhabited α] {a : Array α} {x : α} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

@[expose] def StepE (gs : Array (Array ℕ)) (T : ℕ → Array ℕ) (PA PB C POS : ℕ → ℕ) (n i : ℕ) :
    Prop :=
  i / gs.size < C i ∧ POS i ≤ C i ∧ POS i < n ∧
    T (POS i) = compA (T (i / gs.size)) gs[i % gs.size]! ∧
    (POS i = C i → C (i + 1) = C i + 1 ∧ PA (C i - 1) = i / gs.size ∧ PB (C i - 1) = i % gs.size) ∧
    (POS i ≠ C i → C (i + 1) = C i)

section

variable {gs : Array (Array ℕ)} {T : ℕ → Array ℕ} {PA PB C POS : ℕ → ℕ} {n : ℕ}

theorem inner_step (hd : ∀ t < n, ∀ t' < n, T t = T t' → t = t') {h s : ℕ}
    (hs : StepE gs T PA PB C POS n (h * gs.size + s)) (hsl : s < gs.size) {E : Enum}
    (hE : BInvE T PA PB (C (h * gs.size + s)) E) :
    BInvE T PA PB (C (h * gs.size + s + 1)) (stepJ gs (T h) h E s) := by
  have hk : 0 < gs.size := by omega
  have hdiv : (h * gs.size + s) / gs.size = h := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hsl, Nat.zero_add]
  have hmod : (h * gs.size + s) % gs.size = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsl]
  generalize h * gs.size + s = i at hs hE hdiv hmod ⊢
  obtain ⟨hh, hp1, hp2, hpT, hnew, hold⟩ := hs
  rw [hdiv, hmod] at hpT hnew
  rw [hdiv] at hh
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hE
  have hy : compA (T h) gs[s]! = T (POS i) := hpT.symm
  unfold stepJ
  rw [hy]
  rcases Nat.lt_or_eq_of_le hp1 with hlt | heq
  · have hin : E.index.contains (T (POS i)) = true := (e6 _).2 ⟨POS i, hlt, rfl⟩
    rw [if_neg (by rw [hin]; decide), hold (Nat.ne_of_lt hlt)]
    exact ⟨e1, e2, e3, e4, e5, e6, e7⟩
  · have hout : E.index.contains (T (POS i)) = false := by
      cases hm : E.index.contains (T (POS i))
      · rfl
      · obtain ⟨t, ht, he⟩ := (e6 _).1 hm
        have := hd t (by omega) (POS i) hp2 he
        omega
    obtain ⟨hc1, hc2, hc3⟩ := hnew heq
    rw [if_pos (by rw [hout]; decide), hc1]
    have hc0 : 0 < C i := by omega
    refine ⟨by simp [e1], by simp [e2], by simp [e3], fun t ht => ?_, fun t ht ht0 => ?_,
      fun y => ?_, fun t ht => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · rw [push_lt (by omega)]
        exact e4 t ht
      · subst ht
        have p0 : (E.elems.push (T (POS i)))[C i]! = T (POS i) := by
          rw [← e1]
          exact push_eq
        rw [p0, heq]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · rw [push_lt (by omega), push_lt (by omega)]
        exact e5 t ht ht0
      · subst ht
        have p1 : (E.parent.push h)[C i]! = h := by
          rw [← e2]
          exact push_eq
        have p2 : (E.gen.push s)[C i]! = s := by
          rw [← e3]
          exact push_eq
        rw [p1, p2, hc2, hc3]
        exact ⟨rfl, rfl⟩
    · simp only [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
      rw [e6]
      constructor
      · rintro (h1 | ⟨t, ht, h2⟩)
        · exact ⟨C i, by omega, by rw [← heq, h1]⟩
        · exact ⟨t, by omega, h2⟩
      · rintro ⟨t, ht, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
        · exact Or.inr ⟨t, ht, h2⟩
        · subst ht
          exact Or.inl (by rw [heq, h2])
    · rw [Std.HashMap.getElem?_insert]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · have hne : (T (POS i) == T t) = false := by
          rw [beq_eq_false_iff_ne]
          intro he
          have := hd (POS i) hp2 t (by omega) he
          omega
        rw [hne]
        exact e7 t ht
      · subst ht
        rw [heq, beq_self_eq_true, if_pos rfl, e1]

theorem C_le (hk : 0 < gs.size) (hC0 : C 0 = 1) (hn : 0 < n)
    (hS : ∀ i < n * gs.size, StepE gs T PA PB C POS n i) : ∀ i ≤ n * gs.size, C i ≤ n := by
  intro i hi
  induction i with
  | zero => omega
  | succ i ih =>
    obtain ⟨-, hp1, hp2, -, hnew, hold⟩ := hS i (by omega)
    have := ih (by omega)
    by_cases he : POS i = C i
    · rw [(hnew he).1]
      omega
    · rw [hold he]
      exact this

theorem head_step (hd : ∀ t < n, ∀ t' < n, T t = T t' → t = t') {h : ℕ} (hh : h < n)
    (hS : ∀ i < n * gs.size, StepE gs T PA PB C POS n i) {E : Enum}
    (hE : BInvE T PA PB (C (h * gs.size)) E) (hk : 0 < gs.size) :
    BInvE T PA PB (C ((h + 1) * gs.size)) (outerJ gs E h) := by
  have hlt : h < E.elems.size := by
    rw [hE.1]
    have := (hS (h * gs.size) (by
      have := Nat.mul_le_mul_right gs.size (Nat.succ_le_of_lt hh)
      rw [Nat.succ_mul] at this
      omega)).1
    rwa [Nat.mul_div_cancel _ hk] at this
  unfold outerJ
  rw [if_pos hlt, bfsStep_eq, hE.2.2.2.1 h (by rw [← hE.1]; exact hlt)]
  have key : ∀ s ≤ gs.size, BInvE T PA PB (C (h * gs.size + s))
      ((List.range s).foldl (stepJ gs (T h) h) E) := by
    intro s hs'
    induction s with
    | zero => simpa using hE
    | succ s ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← Nat.add_assoc]
      have hi : h * gs.size + s < n * gs.size := by
        have := Nat.mul_le_mul_right gs.size (Nat.succ_le_of_lt hh)
        rw [Nat.succ_mul] at this
        omega
      exact inner_step hd (hS _ hi) (by omega) (ih (by omega))
  have := key gs.size le_rfl
  rwa [← Nat.succ_mul] at this

theorem init_inv (hT0 : T 0 = idA ()) (hC0 : C 0 = 1) : BInvE T PA PB (C 0) initE := by
  rw [hC0]
  refine ⟨rfl, rfl, rfl, fun t ht => ?_, fun t ht ht0 => by omega, fun y => ?_, fun t ht => ?_⟩
  · have : t = 0 := by omega
    subst this
    rw [hT0]
    rfl
  · simp only [initE, Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
      beq_iff_eq]
    constructor
    · rintro rfl
      exact ⟨0, by omega, hT0⟩
    · rintro ⟨t, ht, h2⟩
      have : t = 0 := by omega
      subst this
      rw [← h2, hT0]
  · have : t = 0 := by omega
    subst this
    simp only [initE, Std.HashMap.getElem?_insert, hT0, beq_self_eq_true, if_true]

theorem foldl_idle : ∀ (l : List ℕ) (E : Enum), (∀ q ∈ l, E.elems.size ≤ q) →
    l.foldl (outerJ gs) E = E
  | [], _, _ => rfl
  | q :: l, E, h => by
    rw [List.foldl_cons]
    have e : outerJ gs E q = E := by
      unfold outerJ
      rw [if_neg (by have := h q List.mem_cons_self; omega)]
    rw [e]
    exact foldl_idle l E fun q' hq' => h q' (List.mem_cons_of_mem q hq')

theorem bfsEnum_replay {fuel : ℕ} (hk : 0 < gs.size) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hT0 : T 0 = idA ()) (hd : ∀ t < n, ∀ t' < n, T t = T t' → t = t') (hC0 : C 0 = 1)
    (hCn : C (n * gs.size) = n) (hS : ∀ i < n * gs.size, StepE gs T PA PB C POS n i) :
    BInvE T PA PB n (bfsEnum gs fuel) := by
  have key : ∀ h ≤ n, BInvE T PA PB (C (h * gs.size))
      ((List.range h).foldl (outerJ gs) initE) := by
    intro h hh
    induction h with
    | zero => simpa using init_inv (PA := PA) (PB := PB) hT0 hC0
    | succ h ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact head_step hd (by omega) hS (ih (by omega)) hk
  have hN := key n le_rfl
  rw [hCn] at hN
  rw [bfsEnum_eq, (by omega : fuel = n + (fuel - n)), List.range_add, List.foldl_append,
    foldl_idle _ _ fun q hq => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hq
      rw [hN.1]
      omega]
  exact hN

theorem lookup_of_inv {E : Enum} (hE : BInvE T PA PB n E) {t : ℕ} (ht : t < n) :
    E.lookup (T t) = some t := by
  unfold Enum.lookup
  rw [hE.2.2.2.2.2.2 t ht]
  simp only
  rw [if_pos ⟨by rw [hE.1]; exact ht, hE.2.2.2.1 t ht⟩]

theorem enumOK_of_replay {fuel : ℕ} (hk : 0 < gs.size) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hT0 : T 0 = idA ()) (hd : ∀ t < n, ∀ t' < n, T t = T t' → t = t') (hC0 : C 0 = 1)
    (hCn : C (n * gs.size) = n) (hS : ∀ i < n * gs.size, StepE gs T PA PB C POS n i)
    (hB : ∀ i < n - 1, PA i ≤ i ∧ PB i < gs.size ∧ T (i + 1) = compA (T (PA i)) gs[PB i]!) :
    enumOK (bfsEnum gs fuel) gs = true := by
  have hE := bfsEnum_replay hk hn hfuel hT0 hd hC0 hCn hS
  obtain ⟨e1, -, -, e4, e5, -, -⟩ := hE
  unfold enumOK treeOK closedOK nodupOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true]
  refine ⟨⟨⟨?_, fun i hi => ?_⟩, fun i hi j hj => ?_⟩, fun i hi => ?_⟩
  · rw [Array.getElem?_eq_getElem (by omega), ← getElem!_pos _ 0 (by omega), e4 0 hn, hT0]
  · rw [e1] at hi
    by_cases h0 : i = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩ <;> obtain ⟨p1, p2⟩ := e5 i hi (by omega) <;>
        obtain ⟨b1, b2, b3⟩ := hB (i - 1) (by omega)
      · rw [p1]
        omega
      · rw [p2]
        exact b2
      · have hi1 : i - 1 + 1 = i := by omega
        rw [hi1] at b3
        rw [p1, p2, e4 i hi, e4 _ (by omega), b3]
  · rw [e1] at hi
    have hs := hS (i * gs.size + j) (by
      have := Nat.mul_le_mul_right gs.size (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at this
      omega)
    have hdiv : (i * gs.size + j) / gs.size = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : (i * gs.size + j) % gs.size = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    obtain ⟨-, -, hp2, hpT, -, -⟩ := hs
    rw [hdiv, hmod] at hpT
    rw [e4 i hi, ← hpT, lookup_of_inv (bfsEnum_replay hk hn hfuel hT0 hd hC0 hCn hS) hp2]
    rfl
  · rw [e1] at hi
    rw [e4 i hi]
    exact lookup_of_inv (bfsEnum_replay hk hn hfuel hT0 hd hC0 hCn hS) hi

end

end CFSG.KC.BfsEnum

end
