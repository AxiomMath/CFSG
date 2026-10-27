module

public import CFSG.Certificates.Kernel.Misc.BfsEnumSound
public import Certificates.Data.Foote82OmegaSixCent

public section

namespace CFSG.KC.ConjEnum

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.CGT.Foote82.OmegaSix CFSG.KC.BfsEnum

@[expose] def cj (gs gsInv : Array (Array ℕ)) (x : Array ℕ) (j : ℕ) : Array ℕ :=
  compA (compA gs[j]! x) gsInv[j]!

@[expose] def stepC (gs gsInv : Array (Array ℕ)) (x : Array ℕ) (q : ℕ) (E : Enum) (j : ℕ) : Enum :=
  if (!E.index.contains (cj gs gsInv x j)) = true then
    ⟨E.elems.push (cj gs gsInv x j), E.parent.push q, E.gen.push j,
      E.index.insert (cj gs gsInv x j) E.elems.size⟩
  else E

@[expose] def outerC (gs gsInv : Array (Array ℕ)) (E : Enum) (q : ℕ) : Enum :=
  if q < E.elems.size then conjStep gs gsInv E q else E

@[expose] def initC (x : Array ℕ) : Enum :=
  ⟨#[x], #[0], #[0], ({} : Std.HashMap (Array ℕ) ℕ).insert x 0⟩

theorem conjStep_eq (gs gsInv : Array (Array ℕ)) (E : Enum) (q : ℕ) :
    conjStep gs gsInv E q = (List.range gs.size).foldl (stepC gs gsInv E.elems[q]! q) E := by
  unfold conjStep
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.range_eq_range', bind_pure]
  exact forIn_foldl _ _ _ _ fun j b => by unfold stepC cj; split <;> rfl

theorem conjEnum_eq (gs gsInv : Array (Array ℕ)) (x : Array ℕ) (fuel : ℕ) :
    conjEnum gs gsInv x fuel = (List.range fuel).foldl (outerC gs gsInv) (initC x) := by
  unfold conjEnum
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.range_eq_range', bind_pure]
  exact forIn_foldl _ _ _ _ fun j b => by unfold outerC; split <;> rfl

@[expose] def StepC (gs gsInv : Array (Array ℕ)) (T : ℕ → Array ℕ) (PA PB C POS : ℕ → ℕ)
    (n i : ℕ) : Prop :=
  i / gs.size < C i ∧ POS i ≤ C i ∧ POS i < n ∧
    T (POS i) = cj gs gsInv (T (i / gs.size)) (i % gs.size) ∧
    (POS i = C i → C (i + 1) = C i + 1 ∧ PA (C i - 1) = i / gs.size ∧ PB (C i - 1) = i % gs.size) ∧
    (POS i ≠ C i → C (i + 1) = C i)

section

variable {gs gsInv : Array (Array ℕ)} {T : ℕ → Array ℕ} {PA PB C POS : ℕ → ℕ} {n : ℕ}

theorem inner_stepC (hd : ∀ t < n, ∀ t' < n, T t = T t' → t = t') {h s : ℕ}
    (hs : StepC gs gsInv T PA PB C POS n (h * gs.size + s)) (hsl : s < gs.size) {E : Enum}
    (hE : BInvE T PA PB (C (h * gs.size + s)) E) :
    BInvE T PA PB (C (h * gs.size + s + 1)) (stepC gs gsInv (T h) h E s) := by
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
  have hy : cj gs gsInv (T h) s = T (POS i) := hpT.symm
  unfold stepC
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

theorem head_stepC (hd : ∀ t < n, ∀ t' < n, T t = T t' → t = t') {h : ℕ} (hh : h < n)
    (hS : ∀ i < n * gs.size, StepC gs gsInv T PA PB C POS n i) {E : Enum}
    (hE : BInvE T PA PB (C (h * gs.size)) E) (hk : 0 < gs.size) :
    BInvE T PA PB (C ((h + 1) * gs.size)) (outerC gs gsInv E h) := by
  have hlt : h < E.elems.size := by
    rw [hE.1]
    have := (hS (h * gs.size) (by
      have := Nat.mul_le_mul_right gs.size (Nat.succ_le_of_lt hh)
      rw [Nat.succ_mul] at this
      omega)).1
    rwa [Nat.mul_div_cancel _ hk] at this
  unfold outerC
  rw [if_pos hlt, conjStep_eq, hE.2.2.2.1 h (by rw [← hE.1]; exact hlt)]
  have key : ∀ s ≤ gs.size, BInvE T PA PB (C (h * gs.size + s))
      ((List.range s).foldl (stepC gs gsInv (T h) h) E) := by
    intro s hs'
    induction s with
    | zero => simpa using hE
    | succ s ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← Nat.add_assoc]
      have hi : h * gs.size + s < n * gs.size := by
        have := Nat.mul_le_mul_right gs.size (Nat.succ_le_of_lt hh)
        rw [Nat.succ_mul] at this
        omega
      exact inner_stepC hd (hS _ hi) (by omega) (ih (by omega))
  have := key gs.size le_rfl
  rwa [← Nat.succ_mul] at this

theorem init_invC {x : Array ℕ} (hT0 : T 0 = x) (hC0 : C 0 = 1) :
    BInvE T PA PB (C 0) (initC x) := by
  rw [hC0]
  refine ⟨rfl, rfl, rfl, fun t ht => ?_, fun t ht ht0 => by omega, fun y => ?_, fun t ht => ?_⟩
  · have : t = 0 := by omega
    subst this
    rw [hT0]
    rfl
  · simp only [initC, Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
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
    simp only [initC, Std.HashMap.getElem?_insert, hT0, beq_self_eq_true, if_true]

theorem foldl_idleC : ∀ (l : List ℕ) (E : Enum), (∀ q ∈ l, E.elems.size ≤ q) →
    l.foldl (outerC gs gsInv) E = E
  | [], _, _ => rfl
  | q :: l, E, h => by
    rw [List.foldl_cons]
    have e : outerC gs gsInv E q = E := by
      unfold outerC
      rw [if_neg (by have := h q List.mem_cons_self; omega)]
    rw [e]
    exact foldl_idleC l E fun q' hq' => h q' (List.mem_cons_of_mem q hq')

theorem conjEnum_replay {x : Array ℕ} {fuel : ℕ} (hk : 0 < gs.size) (hn : 0 < n)
    (hfuel : n ≤ fuel) (hT0 : T 0 = x) (hd : ∀ t < n, ∀ t' < n, T t = T t' → t = t')
    (hC0 : C 0 = 1) (hCn : C (n * gs.size) = n)
    (hS : ∀ i < n * gs.size, StepC gs gsInv T PA PB C POS n i) :
    BInvE T PA PB n (conjEnum gs gsInv x fuel) := by
  have key : ∀ h ≤ n, BInvE T PA PB (C (h * gs.size))
      ((List.range h).foldl (outerC gs gsInv) (initC x)) := by
    intro h hh
    induction h with
    | zero => simpa using init_invC (PA := PA) (PB := PB) hT0 hC0
    | succ h ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact head_stepC hd (by omega) hS (ih (by omega)) hk
  have hN := key n le_rfl
  rw [hCn] at hN
  rw [conjEnum_eq, (by omega : fuel = n + (fuel - n)), List.range_add, List.foldl_append,
    foldl_idleC _ _ fun q hq => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hq
      rw [hN.1]
      omega]
  exact hN

theorem conjTreeOK_of_replay {x : Array ℕ} {fuel : ℕ} (hk : 0 < gs.size) (hn : 0 < n)
    (hfuel : n ≤ fuel) (hT0 : T 0 = x) (hd : ∀ t < n, ∀ t' < n, T t = T t' → t = t')
    (hC0 : C 0 = 1) (hCn : C (n * gs.size) = n)
    (hS : ∀ i < n * gs.size, StepC gs gsInv T PA PB C POS n i)
    (hB : ∀ i < n - 1, PA i ≤ i ∧ PB i < gs.size ∧ T (i + 1) = cj gs gsInv (T (PA i)) (PB i)) :
    conjTreeOK (conjEnum gs gsInv x fuel) gs gsInv x = true := by
  have hE := conjEnum_replay hk hn hfuel hT0 hd hC0 hCn hS
  obtain ⟨e1, -, -, e4, e5, -, -⟩ := hE
  unfold conjTreeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true]
  refine ⟨?_, fun i hi => ?_⟩
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
        rw [p1, p2, e4 i hi, e4 _ (by omega), b3, cj]

end

end CFSG.KC.ConjEnum

end
