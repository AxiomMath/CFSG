module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GroupActions.Exchange

section Alternating

variable {α M : Type*}

@[expose] def altWord (a b : α) : ℕ → List α
  | 0 => []
  | n + 1 => a :: altWord b a n

@[simp] theorem altWord_zero (a b : α) : altWord a b 0 = [] := rfl

@[simp] theorem altWord_succ (a b : α) (n : ℕ) : altWord a b (n + 1) = a :: altWord b a n := rfl

@[simp] theorem length_altWord (a b : α) (n : ℕ) : (altWord a b n).length = n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp [ih]

theorem take_altWord (a b : α) {j n : ℕ} (h : j ≤ n) :
    (altWord a b n).take j = altWord a b j := by
  induction j generalizing a b n with
  | zero => simp
  | succ j ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
    simp [ih b a (by omega : j ≤ n)]

variable [Monoid M]

@[expose] def altProd (a b : M) : ℕ → M
  | 0 => 1
  | n + 1 => a * altProd b a n

@[simp] theorem altProd_zero (a b : M) : altProd a b 0 = 1 := rfl

@[simp] theorem altProd_succ (a b : M) (n : ℕ) : altProd a b (n + 1) = a * altProd b a n := rfl

@[simp] theorem prod_map_altWord (g : α → M) (a b : α) (n : ℕ) :
    ((altWord a b n).map g).prod = altProd (g a) (g b) n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp [ih]

theorem altProd_eq_pow_mul_altProd {G : Type*} [Group G] {s t : G} (hs : s * s = 1)
    (ht : t * t = 1) (n : ℕ) : altProd s t n = (s * t) ^ n * altProd t s n := by
  induction n generalizing s t with
  | zero => simp
  | succ n ih =>
    have hsemi : s * (t * s) ^ n = (s * t) ^ n * s :=
      SemiconjBy.pow_right (show SemiconjBy s (t * s) (s * t) from (mul_assoc s t s).symm) n
    rw [altProd_succ, altProd_succ, ih ht hs, ← mul_assoc, hsemi, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc t t, ht, one_mul]

theorem altProd_eq_altProd_iff {G : Type*} [Group G] {s t : G} (hs : s * s = 1)
    (ht : t * t = 1) {n : ℕ} : altProd s t n = altProd t s n ↔ (s * t) ^ n = 1 := by
  rw [altProd_eq_pow_mul_altProd hs ht n, mul_eq_right]

end Alternating

section Words

variable {W : Type*} [Group W] (S : Set W)

@[expose] def wordProd (l : List S) : W := (l.map Subtype.val).prod

@[expose] noncomputable def wordLength (w : W) : ℕ :=
  sInf {n | ∃ l : List S, l.length = n ∧ wordProd S l = w}

@[expose] def IsReduced (l : List S) : Prop := l.length = wordLength S (wordProd S l)

@[expose] def ExchangeCondition : Prop :=
  ∀ (s : S) (l : List S), IsReduced S l → l ≠ [] →
    wordLength S ((s : W) * wordProd S l) ≤ wordLength S (wordProd S l) →
      ∃ j < l.length, (s : W) * wordProd S (l.take j) = wordProd S (l.take (j + 1))

@[expose] def BraidRel {M : Type*} [Monoid M] (f : S → M) : Prop :=
  ∀ s t : S, s ≠ t → orderOf ((s : W) * t) ≠ 0 →
    altProd (f s) (f t) (orderOf ((s : W) * t)) = altProd (f t) (f s) (orderOf ((s : W) * t))

variable {S}

@[simp] theorem wordProd_nil : wordProd S [] = 1 := rfl

@[simp] theorem wordProd_cons (s : S) (l : List S) :
    wordProd S (s :: l) = s * wordProd S l := rfl

@[simp] theorem wordProd_singleton (s : S) : wordProd S [s] = s := mul_one _

@[simp] theorem wordProd_append (l l' : List S) :
    wordProd S (l ++ l') = wordProd S l * wordProd S l' := by
  simp [wordProd]

theorem wordProd_altWord (s t : S) (n : ℕ) : wordProd S (altWord s t n) = altProd (s : W) t n :=
  prod_map_altWord _ s t n

theorem wordLength_wordProd_le (l : List S) : wordLength S (wordProd S l) ≤ l.length := by
  apply Nat.sInf_le
  exact ⟨l, rfl, rfl⟩

theorem exists_length_eq_wordLength (l : List S) :
    ∃ l' : List S, l'.length = wordLength S (wordProd S l) ∧ wordProd S l' = wordProd S l :=
  Nat.sInf_mem (s := {n | ∃ l' : List S, l'.length = n ∧ wordProd S l' = wordProd S l})
    ⟨l.length, l, rfl, rfl⟩

theorem IsReduced.length_eq {l : List S} (h : IsReduced S l) :
    l.length = wordLength S (wordProd S l) :=
  h

theorem isReduced_iff {l : List S} :
    IsReduced S l ↔ ∀ l' : List S, wordProd S l' = wordProd S l → l.length ≤ l'.length := by
  refine ⟨fun h l' hl' => ?_, fun h => ?_⟩
  · rw [h.length_eq, ← hl']
    exact wordLength_wordProd_le l'
  · obtain ⟨l', hlen, hl'⟩ := exists_length_eq_wordLength l
    exact le_antisymm ((h l' hl').trans hlen.le) (wordLength_wordProd_le l)

theorem IsReduced.length_le {l l' : List S} (h : IsReduced S l)
    (h' : wordProd S l' = wordProd S l) : l.length ≤ l'.length :=
  isReduced_iff.1 h l' h'

theorem IsReduced.nil : IsReduced S [] :=
  isReduced_iff.2 fun _ _ => Nat.zero_le _

theorem IsReduced.length_eq_length {l l' : List S} (h : IsReduced S l) (h' : IsReduced S l')
    (hp : wordProd S l = wordProd S l') : l.length = l'.length :=
  le_antisymm (h.length_le hp.symm) (h'.length_le hp)

theorem IsReduced.of_length_eq {l l' : List S} (h : IsReduced S l)
    (hp : wordProd S l' = wordProd S l) (hlen : l'.length = l.length) : IsReduced S l' :=
  isReduced_iff.2 fun _ h'' => by
    rw [hlen]
    exact h.length_le (h''.trans hp)

theorem IsReduced.of_append_left {l₁ l₂ : List S} (h : IsReduced S (l₁ ++ l₂)) :
    IsReduced S l₁ :=
  isReduced_iff.2 fun l' hl' => by
    have := h.length_le (l' := l' ++ l₂) (by rw [wordProd_append, wordProd_append, hl'])
    rw [List.length_append, List.length_append] at this
    omega

theorem IsReduced.of_append_right {l₁ l₂ : List S} (h : IsReduced S (l₁ ++ l₂)) :
    IsReduced S l₂ :=
  isReduced_iff.2 fun l' hl' => by
    have := h.length_le (l' := l₁ ++ l') (by rw [wordProd_append, wordProd_append, hl'])
    rw [List.length_append, List.length_append] at this
    omega

theorem IsReduced.of_cons {s : S} {l : List S} (h : IsReduced S (s :: l)) : IsReduced S l :=
  IsReduced.of_append_right (l₁ := [s]) h

theorem exists_isReduced_wordProd_eq (l : List S) :
    ∃ l' : List S, IsReduced S l' ∧ wordProd S l' = wordProd S l := by
  obtain ⟨l', hlen, hl'⟩ := exists_length_eq_wordLength l
  refine ⟨l', ?_, hl'⟩
  rw [IsReduced, hl']
  exact hlen

theorem coe_mul_self_eq_one (hS2 : ∀ s ∈ S, orderOf s = 2) (s : S) : (s : W) * s = 1 := by
  rw [← sq, ← hS2 s s.2, pow_orderOf_eq_one]

theorem IsReduced.wordLength_mul_lt (hS2 : ∀ s ∈ S, orderOf s = 2) {s : S} {u : List S}
    (h : IsReduced S (s :: u)) :
    wordLength S ((s : W) * wordProd S (s :: u)) < wordLength S (wordProd S (s :: u)) := by
  rw [← h.length_eq, wordProd_cons, ← mul_assoc, coe_mul_self_eq_one hS2, one_mul,
    List.length_cons]
  exact Nat.lt_succ_of_le (wordLength_wordProd_le u)

theorem IsReduced.ne_nil_of_wordLength_mul_lt {s : S} {l : List S} (hl : IsReduced S l)
    (hs : wordLength S ((s : W) * wordProd S l) < wordLength S (wordProd S l)) : l ≠ [] := by
  rintro rfl
  rw [← hl.length_eq] at hs
  exact Nat.not_lt_zero _ hs

theorem mul_wordProd_eq_wordProd_eraseIdx (hS2 : ∀ s ∈ S, orderOf s = 2) {s : S}
    {l : List S} {j : ℕ} (hj : j < l.length)
    (h : (s : W) * wordProd S (l.take j) = wordProd S (l.take (j + 1))) :
    (s : W) * wordProd S l = wordProd S (l.eraseIdx j) := by
  have hl : l = l.take j ++ [l[j]] ++ l.drop (j + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hj,
      List.take_append_drop]
  rw [List.take_succ_eq_append_getElem hj, wordProd_append, wordProd_singleton] at h
  conv_lhs => rw [hl]
  rw [List.eraseIdx_eq_take_drop_succ]
  simp only [wordProd_append, wordProd_singleton, mul_assoc]
  rw [← mul_assoc (s : W), h, mul_assoc, ← mul_assoc (l[j] : W), coe_mul_self_eq_one hS2,
    one_mul]

theorem exchange_append (hS2 : ∀ s ∈ S, orderOf s = 2) (hex : ExchangeCondition S) {s : S}
    {p σ : List S} (hred : IsReduced S (p ++ σ)) (hne : p ++ σ ≠ [])
    (hs : wordLength S ((s : W) * wordProd S (p ++ σ)) ≤ wordLength S (wordProd S (p ++ σ))) :
    (∃ j < p.length, (s : W) * wordProd S (p.take j) = wordProd S (p.take (j + 1))) ∨
      ∃ σ' : List S, IsReduced S (s :: (p ++ σ')) ∧
        wordProd S (s :: (p ++ σ')) = wordProd S (p ++ σ) := by
  obtain ⟨j, hj, hjeq⟩ := hex s (p ++ σ) hred hne hs
  rcases lt_or_ge j p.length with hjp | hjp
  · refine Or.inl ⟨j, hjp, ?_⟩
    rwa [List.take_append_of_le_length hjp.le, List.take_append_of_le_length hjp] at hjeq
  · have he := mul_wordProd_eq_wordProd_eraseIdx hS2 hj hjeq
    rw [List.eraseIdx_append_of_length_le hjp] at he
    have hjσ : j - p.length < σ.length := by
      rw [List.length_append] at hj
      omega
    have hp : wordProd S (s :: (p ++ σ.eraseIdx (j - p.length))) = wordProd S (p ++ σ) := by
      rw [wordProd_cons, ← he, ← mul_assoc, coe_mul_self_eq_one hS2, one_mul]
    refine Or.inr ⟨σ.eraseIdx (j - p.length), hred.of_length_eq hp ?_, hp⟩
    rw [List.length_cons, List.length_append, List.length_append,
      List.length_eraseIdx_of_lt hjσ]
    omega

theorem altWord_append_step (hS2 : ∀ s ∈ S, orderOf s = 2) (hex : ExchangeCondition S)
    {a b : S} {k : ℕ} {σ : List S} (hred : IsReduced S (altWord b a k ++ σ))
    (ha : wordLength S ((a : W) * wordProd S (altWord b a k ++ σ)) <
      wordLength S (wordProd S (altWord b a k ++ σ))) :
    (∃ n, 0 < n ∧ n ≤ k ∧ wordProd S (altWord a b n) = wordProd S (altWord b a n)) ∨
      ∃ σ' : List S, IsReduced S (altWord a b (k + 1) ++ σ') ∧
        wordProd S (altWord a b (k + 1) ++ σ') = wordProd S (altWord b a k ++ σ) := by
  rcases exchange_append hS2 hex hred (hred.ne_nil_of_wordLength_mul_lt ha) ha.le with
    ⟨j, hj, hjeq⟩ | ⟨σ', hred', hprod'⟩
  · rw [length_altWord] at hj
    rw [take_altWord _ _ hj.le, take_altWord _ _ hj] at hjeq
    exact Or.inl ⟨j + 1, j.succ_pos, hj, by rw [altWord_succ a b, wordProd_cons, hjeq]⟩
  · exact Or.inr ⟨σ', hred', hprod'⟩

theorem exists_isReduced_altWord_append (hS2 : ∀ s ∈ S, orderOf s = 2)
    (hex : ExchangeCondition S) {s t : S} {l : List S} (hl : IsReduced S l)
    (hs : wordLength S ((s : W) * wordProd S l) < wordLength S (wordProd S l))
    (ht : wordLength S ((t : W) * wordProd S l) < wordLength S (wordProd S l)) :
    orderOf ((s : W) * t) ≠ 0 ∧ ∃ σ : List S,
      IsReduced S (altWord s t (orderOf ((s : W) * t)) ++ σ) ∧
        wordProd S (altWord s t (orderOf ((s : W) * t)) ++ σ) = wordProd S l := by
  let Pre : List S → Prop := fun p =>
    ∃ σ : List S, IsReduced S (p ++ σ) ∧ wordProd S (p ++ σ) = wordProd S l
  have step : ∀ (a b : S) (k : ℕ),
      wordLength S ((a : W) * wordProd S l) < wordLength S (wordProd S l) →
        Pre (altWord b a k) →
          (∃ n, 0 < n ∧ n ≤ k ∧ wordProd S (altWord a b n) = wordProd S (altWord b a n)) ∨
            Pre (altWord a b (k + 1)) := by
    rintro a b k ha ⟨σ, hred, hprod⟩
    rw [← hprod] at ha
    rcases altWord_append_step hS2 hex hred ha with h | ⟨σ', hred', hprod'⟩
    · exact Or.inl h
    · exact Or.inr ⟨σ', hred', hprod'.trans hprod⟩
  have key : ∀ k, (Pre (altWord s t k) ∧ Pre (altWord t s k)) ∨ ∃ k n, 0 < n ∧ n ≤ k ∧
      Pre (altWord s t k) ∧ wordProd S (altWord s t n) = wordProd S (altWord t s n) := by
    intro k
    induction k with
    | zero => exact Or.inl ⟨⟨l, hl, rfl⟩, ⟨l, hl, rfl⟩⟩
    | succ k ih =>
      rcases ih with ⟨h1, h2⟩ | hQ
      · rcases step s t k hs h2 with ⟨n, hn, hnk, heq⟩ | h1'
        · exact Or.inr ⟨k, n, hn, hnk, h1, heq⟩
        rcases step t s k ht h1 with ⟨n, hn, hnk, heq⟩ | h2'
        · exact Or.inr ⟨k, n, hn, hnk, h1, heq.symm⟩
        exact Or.inl ⟨h1', h2'⟩
      · exact Or.inr hQ
  rcases key (wordLength S (wordProd S l) + 1) with
    ⟨⟨σ, hred, hprod⟩, -⟩ | ⟨k, n, hn, hnk, ⟨σ, hred, hprod⟩, heq⟩
  · have := hred.length_eq
    rw [hprod, List.length_append, length_altWord] at this
    omega
  · rw [wordProd_altWord, wordProd_altWord, altProd_eq_altProd_iff (coe_mul_self_eq_one hS2 s)
      (coe_mul_self_eq_one hS2 t), ← orderOf_dvd_iff_pow_eq_one] at heq
    have hmk : orderOf ((s : W) * t) ≤ k := (Nat.le_of_dvd hn heq).trans hnk
    refine ⟨fun h0 => ?_, (altWord s t k).drop (orderOf ((s : W) * t)) ++ σ, ?_⟩
    · rw [h0, zero_dvd_iff] at heq
      omega
    · rw [← List.append_assoc, ← take_altWord s t hmk, List.take_append_drop]
      exact ⟨hred, hprod⟩

theorem matsumoto_braid_invariance (hS2 : ∀ s ∈ S, orderOf s = 2) (hex : ExchangeCondition S)
    {M : Type*} [Monoid M] (f : S → M) (hf : BraidRel S f) {l l' : List S}
    (hl : IsReduced S l) (hl' : IsReduced S l') (h : wordProd S l = wordProd S l') :
    (l.map f).prod = (l'.map f).prod := by
  obtain ⟨n, hn⟩ : ∃ n, l.length = n := ⟨_, rfl⟩
  induction n generalizing l l' with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 hn
    obtain rfl := List.length_eq_zero_iff.1 ((hl.length_eq_length hl' h).symm.trans hn)
    rfl
  | succ n ih =>
    have head : ∀ (a : S) (x y : List S), x.length = n → IsReduced S (a :: x) →
        IsReduced S (a :: y) → wordProd S (a :: x) = wordProd S (a :: y) →
          ((a :: x).map f).prod = ((a :: y).map f).prod := by
      intro a x y hx hax hay hxy
      rw [wordProd_cons, wordProd_cons, mul_right_inj] at hxy
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
        ih hax.of_cons hay.of_cons hxy hx]
    have hn' : l'.length = n + 1 := (hl.length_eq_length hl' h).symm.trans hn
    obtain ⟨s, u, rfl⟩ := List.exists_cons_of_length_eq_add_one hn
    obtain ⟨t, v, rfl⟩ := List.exists_cons_of_length_eq_add_one hn'
    have hu : u.length = n := by simpa using hn
    have hv : v.length = n := by simpa using hn'
    by_cases hst : s = t
    · subst hst
      exact head s u v hu hl hl' h
    have hdt := hl'.wordLength_mul_lt hS2
    rw [← h] at hdt
    obtain ⟨hm, σ, hA, hAp⟩ :=
      exists_isReduced_altWord_append hS2 hex hl (hl.wordLength_mul_lt hS2) hdt
    have hBp : wordProd S (altWord t s (orderOf ((s : W) * t)) ++ σ) = wordProd S (s :: u) := by
      rw [← hAp, wordProd_append, wordProd_append, wordProd_altWord, wordProd_altWord,
        (altProd_eq_altProd_iff (coe_mul_self_eq_one hS2 s) (coe_mul_self_eq_one hS2 t)).2
          (pow_orderOf_eq_one _)]
    have hB := hA.of_length_eq (hBp.trans hAp.symm) (by simp)
    have hAB : ((altWord s t (orderOf ((s : W) * t)) ++ σ).map f).prod =
        ((altWord t s (orderOf ((s : W) * t)) ++ σ).map f).prod := by
      rw [List.map_append, List.map_append, List.prod_append, List.prod_append, prod_map_altWord,
        prod_map_altWord, hf s t hst hm]
    obtain ⟨m, hm'⟩ := Nat.exists_eq_add_one_of_ne_zero hm
    rw [hm'] at hA hAp hB hBp hAB
    calc ((s :: u).map f).prod = ((altWord s t (m + 1) ++ σ).map f).prod :=
          head s u (altWord t s m ++ σ) hu hl hA hAp.symm
      _ = ((altWord t s (m + 1) ++ σ).map f).prod := hAB
      _ = ((t :: v).map f).prod :=
          (head t v (altWord s t m ++ σ) hv hl' hB (hBp.trans h).symm).symm

end Words

end CFSG.GroupActions.Exchange
