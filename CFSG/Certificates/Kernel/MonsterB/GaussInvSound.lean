module

public import CFSG.Monster.B.TwoA.Unitary.TwentyAlgInputs

public section

namespace CFSG.KC.U20

open CFSG.Monster.B.TwoA.Unitary

@[expose] def selXor (n : ℕ) (rows : Array ℕ) (s : ℕ) : ℕ :=
  (List.range n).foldl (fun acc j => if s.testBit j then acc ^^^ rows[j]! else acc) 0

private def giInit (n : ℕ) (rows : Array ℕ) : Array (ℕ × ℕ) :=
  ((List.range n).map fun i => (rows[i]!, 1 <<< i)).toArray

private def giPivot (n c : ℕ) (A : Array (ℕ × ℕ)) : ℕ :=
  (List.range' c (n - c)).foldl
    (fun p r => if (p == n && (A[r]!).1.testBit c) = true then r else p) n

private def giElim (c : ℕ) (A : Array (ℕ × ℕ)) (r : ℕ) : Array (ℕ × ℕ) :=
  if (r != c && (A[r]!).1.testBit c) = true then
    A.set! r ((A[r]!).1 ^^^ (A[c]!).1, (A[r]!).2 ^^^ (A[c]!).2)
  else A

private def giStep (n : ℕ) (A : Array (ℕ × ℕ)) (c : ℕ) : Array (ℕ × ℕ) :=
  if giPivot n c A < n then
    (List.range' 0 n).foldl (giElim c)
      ((A.set! c A[giPivot n c A]!).set! (giPivot n c A) A[c]!)
  else A

private theorem gi_ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then pure (ForInStep.yield a) else pure (ForInStep.yield b) : Id (ForInStep β)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

private theorem gi_eq_fold (n : ℕ) (rows : Array ℕ) :
    gaussInv n rows = ((List.range' 0 n).foldl (giStep n) (giInit n rows)).map (·.2) := by
  simp only [gaussInv, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, gi_ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind,
    Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero, Prod.mk.eta, giStep, giElim, giPivot, giInit]
  rfl

private theorem gi_get_set {M : Array (ℕ × ℕ)} {n : ℕ} (hM : M.size = n) {i j : ℕ} (hj : j < n)
    (v : ℕ × ℕ) : (M.set! i v)[j]! = if i = j then v else M[j]! := by
  have hj' : j < M.size := by omega
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (M.setIfInBounds i v) j (by simp [hj']),
    Array.getElem_setIfInBounds hj', getElem!_pos M j hj']

private theorem gi_size_set (M : Array (ℕ × ℕ)) (i : ℕ) (v : ℕ × ℕ) :
    (M.set! i v).size = M.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

private theorem gi_selXor_zero (rows : Array ℕ) (s : ℕ) : selXor 0 rows s = 0 := rfl

private theorem gi_selXor_succ (rows : Array ℕ) (s k : ℕ) :
    selXor (k + 1) rows s = selXor k rows s ^^^ (if s.testBit k then rows[k]! else 0) := by
  unfold selXor
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  by_cases h : s.testBit k = true <;> simp [h]

private theorem gi_selXor_xor (rows : Array ℕ) (s t : ℕ) : ∀ k,
    selXor k rows (s ^^^ t) = selXor k rows s ^^^ selXor k rows t
  | 0 => by simp [gi_selXor_zero]
  | k + 1 => by
    rw [gi_selXor_succ, gi_selXor_succ, gi_selXor_succ, gi_selXor_xor rows s t k,
      Nat.testBit_xor]
    generalize selXor k rows s = X
    generalize selXor k rows t = Y
    generalize rows[k]! = r
    cases s.testBit k <;> cases t.testBit k <;> simp
    · ac_rfl
    · ac_rfl
    · apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_xor]
      generalize X.testBit i = a
      generalize Y.testBit i = b
      generalize r.testBit i = c
      revert a b c
      decide

private theorem gi_selXor_pow (rows : Array ℕ) (i : ℕ) : ∀ k,
    selXor k rows (2 ^ i) = if i < k then rows[i]! else 0
  | 0 => by simp [gi_selXor_zero]
  | k + 1 => by
    rw [gi_selXor_succ, gi_selXor_pow rows i k, Nat.testBit_two_pow]
    rcases lt_trichotomy i k with h | h | h
    · have h1 : i ≠ k := by omega
      simp [h, h1, show i < k + 1 by omega]
    · subst h
      simp
    · have h1 : i ≠ k := by omega
      simp [show ¬ i < k by omega, h1, show ¬ i < k + 1 by omega]

private def GiLin (φ : ℕ → Bool) : Prop := ∀ x y, φ (x ^^^ y) = (φ x ^^ φ y)

private theorem gi_lin_zero {φ : ℕ → Bool} (h : GiLin φ) : φ 0 = false := by
  have := h 0 0
  simpa using this

private theorem gi_selXor_lin {φ : ℕ → Bool} (hφ : GiLin φ) (rows : Array ℕ) (s : ℕ) : ∀ k,
    (∀ j < k, φ rows[j]! = false) → φ (selXor k rows s) = false
  | 0, _ => by simpa [gi_selXor_zero] using gi_lin_zero hφ
  | k + 1, h => by
    rw [gi_selXor_succ, hφ, gi_selXor_lin hφ rows s k (fun j hj => h j (by omega))]
    by_cases hb : s.testBit k = true
    · simp [hb, h k (by omega)]
    · simp [hb, gi_lin_zero hφ]

private def giPhi (b : ℕ) (a : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, x => x.testBit b
  | m + 1, x => giPhi b a m x ^^ (x.testBit m && a m)

private theorem giPhi_lin (b : ℕ) (a : ℕ → Bool) : ∀ m, GiLin (giPhi b a m)
  | 0 => fun x y => by simp [giPhi]
  | m + 1 => fun x y => by
    simp only [giPhi, giPhi_lin b a m x y, Nat.testBit_xor]
    generalize giPhi b a m x = p
    generalize giPhi b a m y = q
    generalize x.testBit m = u
    generalize y.testBit m = v
    generalize a m = w
    revert p q u v w
    decide

private theorem giPhi_eval (b : ℕ) (a : ℕ → Bool) (i x : ℕ) : ∀ m,
    (∀ j < m, x.testBit j = decide (i = j)) →
      giPhi b a m x = (x.testBit b ^^ (decide (i < m) && a i))
  | 0, _ => by simp [giPhi]
  | m + 1, h => by
    have ih := giPhi_eval b a i x m (fun j hj => h j (by omega))
    have hm := h m (by omega)
    simp only [giPhi, ih, hm]
    rcases lt_trichotomy i m with h1 | h1 | h1
    · have h2 : i ≠ m := by omega
      simp [h1, h2, show i < m + 1 by omega]
    · subst h1
      simp
    · have h2 : i ≠ m := by omega
      simp [show ¬ i < m by omega, h2, show ¬ i < m + 1 by omega]

private theorem giPhi_pow (b : ℕ) (a : ℕ → Bool) (c : ℕ) : ∀ m,
    giPhi b a m (2 ^ c) = (decide (c = b) ^^ (decide (c < m) && a c))
  | 0 => by simp [giPhi, Nat.testBit_two_pow]
  | m + 1 => by
    simp only [giPhi, giPhi_pow b a c m, Nat.testBit_two_pow]
    rcases lt_trichotomy c m with h1 | h1 | h1
    · have h2 : c ≠ m := by omega
      simp [h1, h2, show c < m + 1 by omega]
    · subst h1
      simp
    · have h2 : c ≠ m := by omega
      simp [show ¬ c < m by omega, h2, show ¬ c < m + 1 by omega]

private def GiCol (n : ℕ) (A : Array (ℕ × ℕ)) (m : ℕ) : Prop :=
  ∀ j < m, ∀ i < n, (A[i]!).1.testBit j = decide (i = j)

private def GiUnits (n : ℕ) (A : Array (ℕ × ℕ)) : Prop :=
  ∀ φ : ℕ → Bool, GiLin φ → (∀ i < n, φ (A[i]!).1 = false) → ∀ c < n, φ (2 ^ c) = false

private def GiGood (n : ℕ) (rows : Array ℕ) (A : Array (ℕ × ℕ)) : Prop :=
  A.size = n ∧ (∀ i < n, (A[i]!).1 = selXor n rows (A[i]!).2) ∧ GiUnits n A

private theorem gi_units_of_cov {n : ℕ} {A A' : Array (ℕ × ℕ)} (hU : GiUnits n A)
    (hcov : ∀ φ, GiLin φ → (∀ j < n, φ (A'[j]!).1 = false) → ∀ i < n, φ (A[i]!).1 = false) :
    GiUnits n A' := fun φ hφ hv c hc => hU φ hφ (hcov φ hφ hv) c hc

private theorem gi_key {n : ℕ} {A : Array (ℕ × ℕ)} (hU : GiUnits n A) {m b : ℕ}
    (hC : ∀ j < m, ∀ i < n, (A[i]!).1.testBit j = decide (i = j))
    (hz : ∀ i, m ≤ i → i < n → (A[i]!).1.testBit b = false) :
    ∀ c < n, decide (c = b) = (decide (c < m) && (A[c]!).1.testBit b) := by
  intro c hc
  have hvan : ∀ i < n, giPhi b (fun j => (A[j]!).1.testBit b) m (A[i]!).1 = false := by
    intro i hi
    rw [giPhi_eval b _ i _ m (fun j hj => hC j hj i hi)]
    by_cases him : i < m
    · simp [him]
    · have := hz i (by omega) hi
      simp [him, this]
  have := hU _ (giPhi_lin b _ m) hvan c hc
  rw [giPhi_pow] at this
  simpa using this

private theorem gi_nopivot {n c : ℕ} {A : Array (ℕ × ℕ)} (hU : GiUnits n A) (hc : c < n)
    (hC : ∀ j < c, ∀ i < n, (A[i]!).1.testBit j = decide (i = j))
    (hz : ∀ i, c ≤ i → i < n → (A[i]!).1.testBit c = false) : False := by
  have := gi_key hU hC hz c hc
  simp at this

private theorem gi_final {n : ℕ} {A : Array (ℕ × ℕ)} (hU : GiUnits n A)
    (hC : ∀ j < n, ∀ i < n, (A[i]!).1.testBit j = decide (i = j)) :
    ∀ c < n, (A[c]!).1 = 2 ^ c := by
  intro c hc
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_two_pow]
  have := gi_key hU (m := n) (b := k) hC (fun i h1 h2 => absurd h2 (by omega)) c hc
  simpa [hc] using this.symm

private theorem gi_find (n : ℕ) (P : ℕ → Bool) : ∀ (L : List ℕ) (q : ℕ), (∀ x ∈ L, x < n) →
    (q ≠ n → L.foldl (fun p r => if (p == n && P r) = true then r else p) q = q) ∧
    (q = n → (L.foldl (fun p r => if (p == n && P r) = true then r else p) q = n ∧
        ∀ x ∈ L, P x = false) ∨
      (L.foldl (fun p r => if (p == n && P r) = true then r else p) q ∈ L ∧
        P (L.foldl (fun p r => if (p == n && P r) = true then r else p) q) = true))
  | [], q, _ => ⟨fun _ => rfl, fun h => Or.inl ⟨h, by simp⟩⟩
  | x :: L, q, hL => by
    have hx : x < n := hL x List.mem_cons_self
    have hL' : ∀ y ∈ L, y < n := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    rw [List.foldl_cons]
    by_cases hq : q = n
    · have hqx : (q == n) = true := by simp [hq]
      by_cases hP : P x = true
      · have e : (if (q == n && P x) = true then x else q) = x := by simp [hqx, hP]
        rw [e, (gi_find n P L x hL').1 (by omega)]
        exact ⟨fun h => absurd hq h, fun _ => Or.inr ⟨List.mem_cons_self, hP⟩⟩
      · have e : (if (q == n && P x) = true then x else q) = q := by simp [hqx, hP]
        rw [e]
        obtain ⟨_, h2⟩ := gi_find n P L q hL'
        refine ⟨fun h => absurd hq h, fun _ => ?_⟩
        rcases h2 hq with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · refine Or.inl ⟨h3, fun y hy => ?_⟩
          rcases List.mem_cons.1 hy with rfl | hy
          · simpa using hP
          · exact h4 y hy
        · exact Or.inr ⟨List.mem_cons_of_mem _ h3, h4⟩
    · have hqx : (q == n) = false := by simpa using hq
      have e : (if (q == n && P x) = true then x else q) = q := by simp [hqx]
      rw [e]
      obtain ⟨h1, _⟩ := gi_find n P L q hL'
      exact ⟨fun _ => h1 hq, fun h => absurd h hq⟩

private theorem gi_pivot_spec {n c : ℕ} (hc : c < n) (A : Array (ℕ × ℕ)) :
    (giPivot n c A < n → c ≤ giPivot n c A ∧ (A[giPivot n c A]!).1.testBit c = true) ∧
    (¬ giPivot n c A < n → ∀ r, c ≤ r → r < n → (A[r]!).1.testBit c = false) := by
  have hL : ∀ x ∈ List.range' c (n - c), x < n := fun x hx => by
    rw [List.mem_range'_1] at hx
    omega
  obtain ⟨_, h2⟩ := gi_find n (fun r => (A[r]!).1.testBit c) (List.range' c (n - c)) n hL
  have h3 := h2 rfl
  unfold giPivot
  rcases h3 with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · rw [h4]
    refine ⟨fun h => absurd h (lt_irrefl n), fun _ r hr1 hr2 => h5 r ?_⟩
    rw [List.mem_range'_1]
    omega
  · refine ⟨fun _ => ⟨?_, h5⟩, fun h => absurd ?_ h⟩
    · exact (List.mem_range'_1.1 h4).1
    · have := (List.mem_range'_1.1 h4).2
      omega

private theorem gi_swap_get {A : Array (ℕ × ℕ)} {n : ℕ} (hA : A.size = n) {p c t : ℕ}
    (ht : t < n) : ((A.set! c A[p]!).set! p A[c]!)[t]! =
      if p = t then A[c]! else if c = t then A[p]! else A[t]! := by
  have h1 : (A.set! c A[p]!).size = n := by rw [gi_size_set, hA]
  rw [gi_get_set h1 ht, gi_get_set hA ht]

private theorem gi_swap_good {n : ℕ} {rows : Array ℕ} {A : Array (ℕ × ℕ)} (hG : GiGood n rows A)
    {c p : ℕ} (hc : c < n) (hp : p < n) :
    GiGood n rows ((A.set! c A[p]!).set! p A[c]!) := by
  obtain ⟨hA, hrec, hU⟩ := hG
  refine ⟨by rw [gi_size_set, gi_size_set, hA], fun t ht => ?_, ?_⟩
  · rw [gi_swap_get hA ht]
    split_ifs
    · exact hrec c hc
    · exact hrec p hp
    · exact hrec t ht
  · refine gi_units_of_cov hU fun φ hφ hv i hi => ?_
    by_cases h1 : i = c
    · have := hv p hp
      rw [gi_swap_get hA hp, if_pos rfl] at this
      rw [h1]
      exact this
    · by_cases h2 : i = p
      · have := hv c hc
        rw [gi_swap_get hA hc, if_neg (by omega), if_pos rfl] at this
        rw [h2]
        exact this
      · have := hv i hi
        rw [gi_swap_get hA hi, if_neg (by omega), if_neg (by omega)] at this
        exact this

private theorem gi_swap_col {n : ℕ} {A : Array (ℕ × ℕ)} (hA : A.size = n) {c p : ℕ}
    (hc : c < n) (hp : p < n) (hcp : c ≤ p) (hC : GiCol n A c) :
    GiCol n ((A.set! c A[p]!).set! p A[c]!) c := by
  intro j hj i hi
  rw [gi_swap_get hA hi]
  split_ifs with h1 h2
  · rw [hC j hj c hc]
    simp only [decide_eq_decide]
    omega
  · rw [hC j hj p hp]
    simp only [decide_eq_decide]
    omega
  · exact hC j hj i hi

private theorem gi_elim_fold {n c : ℕ} (hc : c < n) {B : Array (ℕ × ℕ)} (hB : B.size = n) :
    ∀ k ≤ n, ((List.range' 0 k).foldl (giElim c) B).size = n ∧
      ∀ t < n, ((List.range' 0 k).foldl (giElim c) B)[t]! =
        if t < k ∧ t ≠ c ∧ (B[t]!).1.testBit c = true then
          ((B[t]!).1 ^^^ (B[c]!).1, (B[t]!).2 ^^^ (B[c]!).2) else B[t]!
  | 0, _ => ⟨hB, fun t _ => by simp⟩
  | k + 1, hk => by
    obtain ⟨hs, hget⟩ := gi_elim_fold hc hB k (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    generalize (List.range' 0 k).foldl (giElim c) B = Bk at hs hget
    have hkn : k < n := by omega
    have hBk : Bk[k]! = B[k]! := by rw [hget k hkn]; simp
    have hBc : Bk[c]! = B[c]! := by rw [hget c hc]; simp
    unfold giElim
    rw [hBk, hBc]
    by_cases hcond : (k != c && (B[k]!).1.testBit c) = true
    · rw [if_pos hcond]
      have hcond' : k ≠ c ∧ (B[k]!).1.testBit c = true := by simpa using hcond
      refine ⟨by rw [gi_size_set, hs], fun t ht => ?_⟩
      rw [gi_get_set hs ht]
      by_cases e : k = t
      · subst e
        rw [if_pos rfl, if_pos ⟨by omega, hcond'⟩]
      · rw [if_neg e, hget t ht]
        have h3 : (t < k + 1) ↔ (t < k) := by omega
        simp only [h3]
    · rw [if_neg hcond]
      refine ⟨hs, fun t ht => ?_⟩
      by_cases e : k = t
      · subst e
        rw [hBk, if_neg]
        intro h
        exact hcond (by simpa using h.2)
      · rw [hget t ht]
        have h3 : (t < k + 1) ↔ (t < k) := by omega
        simp only [h3]

private theorem gi_elim_all {n c : ℕ} (hc : c < n) {B : Array (ℕ × ℕ)} (hB : B.size = n) :
    ((List.range' 0 n).foldl (giElim c) B).size = n ∧
      ∀ t < n, ((List.range' 0 n).foldl (giElim c) B)[t]! =
        if t ≠ c ∧ (B[t]!).1.testBit c = true then
          ((B[t]!).1 ^^^ (B[c]!).1, (B[t]!).2 ^^^ (B[c]!).2) else B[t]!  := by
  obtain ⟨h1, h2⟩ := gi_elim_fold hc hB n le_rfl
  exact ⟨h1, fun t ht => by rw [h2 t ht]; simp [ht]⟩

private theorem gi_elim_good {n c : ℕ} {rows : Array ℕ} (hc : c < n) {B : Array (ℕ × ℕ)}
    (hG : GiGood n rows B) (hC : GiCol n B c) (hbit : (B[c]!).1.testBit c = true) :
    GiGood n rows ((List.range' 0 n).foldl (giElim c) B) ∧
      GiCol n ((List.range' 0 n).foldl (giElim c) B) (c + 1) := by
  obtain ⟨hB, hrec, hU⟩ := hG
  obtain ⟨hs, hget⟩ := gi_elim_all hc hB
  have hrl : ∀ j < c, (B[c]!).1.testBit j = false := fun j hj => by
    rw [hC j hj c hc]
    simp only [decide_eq_false_iff_not]
    omega
  generalize (List.range' 0 n).foldl (giElim c) B = A' at hs hget
  have hBc : A'[c]! = B[c]! := by rw [hget c hc]; simp
  refine ⟨⟨hs, fun t ht => ?_, ?_⟩, fun j hj i hi => ?_⟩
  · rw [hget t ht]
    split_ifs
    · dsimp only
      rw [gi_selXor_xor, ← hrec t ht, ← hrec c hc]
    · exact hrec t ht
  · refine gi_units_of_cov hU fun φ hφ hv i hi => ?_
    have hvc := hv c hc
    rw [hBc] at hvc
    have hvi := hv i hi
    rw [hget i hi] at hvi
    split_ifs at hvi with h
    · dsimp only at hvi
      rw [show φ ((B[i]!).1 ^^^ (B[c]!).1) = (φ (B[i]!).1 ^^ φ (B[c]!).1) from hφ _ _, hvc,
        Bool.xor_false] at hvi
      exact hvi
    · exact hvi
  · rw [hget i hi]
    by_cases hjc : j < c
    · split_ifs
      · dsimp only
        rw [Nat.testBit_xor, hrl j hjc, Bool.xor_false]
        exact hC j hjc i hi
      · exact hC j hjc i hi
    · have hjc' : j = c := by omega
      rw [hjc']
      by_cases hic : i = c
      · rw [if_neg (fun h => h.1 hic), hic]
        simp [hbit]
      · by_cases hbi : (B[i]!).1.testBit c = true
        · rw [if_pos ⟨hic, hbi⟩]
          dsimp only
          rw [Nat.testBit_xor, hbi, hbit]
          simp [hic]
        · rw [if_neg (fun h => hbi h.2)]
          have hbi' : (B[i]!).1.testBit c = false := by simpa using hbi
          rw [hbi']
          simp [hic]

private theorem gi_init_good {n : ℕ} {rows : Array ℕ} {D : ℕ → ℕ}
    (hD : ∀ c < n, selXor n rows (D c) = 2 ^ c) : GiGood n rows (giInit n rows) := by
  have hget : ∀ i < n, (giInit n rows)[i]! = (rows[i]!, 2 ^ i) := by
    intro i hi
    simp [giInit, hi, Nat.one_shiftLeft]
  refine ⟨by simp [giInit], fun i hi => ?_, fun φ hφ hv c hc => ?_⟩
  · rw [hget i hi]
    dsimp only
    rw [gi_selXor_pow, if_pos hi]
  · rw [← hD c hc]
    refine gi_selXor_lin hφ rows (D c) n fun j hj => ?_
    have := hv j hj
    rwa [hget j hj] at this

private theorem gi_step {n : ℕ} {rows : Array ℕ} {A : Array (ℕ × ℕ)} {c : ℕ} (hc : c < n)
    (hG : GiGood n rows A) (hC : GiCol n A c) :
    GiGood n rows (giStep n A c) ∧ GiCol n (giStep n A c) (c + 1) := by
  obtain ⟨hp1, hp2⟩ := gi_pivot_spec hc A
  unfold giStep
  by_cases hp : giPivot n c A < n
  · rw [if_pos hp]
    obtain ⟨hcp, hbit⟩ := hp1 hp
    generalize giPivot n c A = p at hp hcp hbit ⊢
    have hA := hG.1
    have hBc : ((A.set! c A[p]!).set! p A[c]!)[c]! = A[p]! := by
      rw [gi_swap_get hA hc]
      by_cases e : p = c
      · rw [if_pos e, e]
      · rw [if_neg e, if_pos rfl]
    exact gi_elim_good hc (gi_swap_good hG hc hp) (gi_swap_col hA hc hp hcp hC)
      (by rw [hBc]; exact hbit)
  · rw [if_neg hp]
    exact (gi_nopivot hG.2.2 hc hC (fun r h1 h2 => hp2 hp r h1 h2)).elim

private theorem gi_fold {n : ℕ} {rows : Array ℕ} {D : ℕ → ℕ}
    (hD : ∀ c < n, selXor n rows (D c) = 2 ^ c) : ∀ k ≤ n,
    GiGood n rows ((List.range' 0 k).foldl (giStep n) (giInit n rows)) ∧
      GiCol n ((List.range' 0 k).foldl (giStep n) (giInit n rows)) k
  | 0, _ => ⟨gi_init_good hD, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, hk => by
    obtain ⟨hG, hC⟩ := gi_fold hD k (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    exact gi_step (by omega) hG hC

theorem gaussInv_spec (n : ℕ) (rows : Array ℕ) (D : ℕ → ℕ)
    (hD : ∀ c < n, selXor n rows (D c) = 2 ^ c) :
    ∀ c < n, selXor n rows ((gaussInv n rows)[c]!) = 2 ^ c := by
  intro c hc
  obtain ⟨⟨hs, hrec, hU⟩, hC⟩ := gi_fold hD n le_rfl
  rw [gi_eq_fold]
  generalize (List.range' 0 n).foldl (giStep n) (giInit n rows) = A at hs hrec hU hC
  have hmap : (A.map (·.2))[c]! = (A[c]!).2 := by
    rw [getElem!_pos (A.map (·.2)) c (by simp [hs, hc]), Array.getElem_map,
      getElem!_pos A c (by omega)]
  rw [hmap, ← hrec c hc, gi_final hU hC c hc]

end CFSG.KC.U20

end
