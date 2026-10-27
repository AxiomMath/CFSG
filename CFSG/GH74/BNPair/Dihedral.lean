module

public import CFSG.GH74.BNPair.Length

public section

namespace CFSG.GH74.BNPair

variable {W : Type*} [Group W]

section AltWord

variable {x y : W}

theorem altWord_zero (x y : W) : altWord x y 0 = 1 := rfl

theorem altWord_succ (x y : W) (i : ℕ) : altWord x y (i + 1) = altWord y x i * x := rfl

theorem altWord_two_add (x y : W) (i : ℕ) :
    altWord x y (i + 2) = altWord x y i * (y * x) := by
  rw [altWord_succ, altWord_succ, mul_assoc]

theorem altWord_one (x y : W) : altWord x y 1 = x := by
  simp [altWord_succ, altWord_zero]

theorem altWord_two_mul (x y : W) (k : ℕ) : altWord x y (2 * k) = (y * x) ^ k := by
  induction k with
  | zero => simp [altWord_zero]
  | succ k ih =>
    have : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [this, altWord_two_add, ih, pow_succ]

theorem altWord_two_mul_add_one (x y : W) (k : ℕ) :
    altWord x y (2 * k + 1) = x * (y * x) ^ k := by
  induction k with
  | zero => simp [altWord_one]
  | succ k ih =>
    have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [this, altWord_two_add, ih, mul_assoc, ← pow_succ]

theorem altWord_succ_left (x y : W) (i : ℕ) :
    altWord x y (i + 1) = (if Even i then x else y) * altWord x y i := by
  induction i generalizing x y with
  | zero => simp [altWord_zero, altWord_one]
  | succ i ih =>
    rw [altWord_succ, ih y x, mul_assoc, ← altWord_succ]
    by_cases h : Even i
    · have h' : ¬ Even (i + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h']
    · have h' : Even (i + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h']

theorem mul_altWord_even (i : ℕ) (hi : Even i) : x * altWord x y i = altWord x y (i + 1) := by
  rw [altWord_succ_left]
  simp [hi]

theorem mul_altWord_odd (i : ℕ) (hi : ¬ Even i) : y * altWord x y i = altWord x y (i + 1) := by
  rw [altWord_succ_left]
  simp [hi]

theorem mul_altWord_odd' (hx : x * x = 1) (i : ℕ) (hi : ¬ Even i) :
    x * altWord x y i = altWord x y (i - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by
    have : i ≠ 0 := by rintro rfl; exact hi (by simp)
    omega⟩
  have hj : Even j := by simpa [Nat.even_add_one] using hi
  rw [altWord_succ_left]
  simp [hj, ← mul_assoc, hx]

theorem mul_altWord_even' (hy : y * y = 1) (i : ℕ) (hi : Even i) (hi0 : i ≠ 0) :
    y * altWord x y i = altWord x y (i - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : ¬ Even j := by simpa [Nat.even_add_one] using hi
  rw [altWord_succ_left]
  simp [hj, ← mul_assoc, hy]

end AltWord

structure IsDihedralGen (a b : W) (n : ℕ) : Prop where
  mul_self_a : a * a = 1
  mul_self_b : b * b = 1
  ne : a ≠ b
  closure_eq : Subgroup.closure ({a, b} : Set W) = ⊤
  card_eq : Nat.card W = 2 * n
  three_le : 3 ≤ n

section Dihedral

variable {a b : W} {n : ℕ}

theorem IsDihedralGen.inv_a (h : IsDihedralGen a b n) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right h.mul_self_a

theorem IsDihedralGen.inv_b (h : IsDihedralGen a b n) : b⁻¹ = b :=
  inv_eq_of_mul_eq_one_right h.mul_self_b

theorem IsDihedralGen.mul_mul_a (h : IsDihedralGen a b n) (z : W) : a * (a * z) = z := by
  rw [← mul_assoc, h.mul_self_a, one_mul]

theorem IsDihedralGen.mul_mul_b (h : IsDihedralGen a b n) (z : W) : b * (b * z) = z := by
  rw [← mul_assoc, h.mul_self_b, one_mul]

theorem IsDihedralGen.a_mul_r_mul_a (h : IsDihedralGen a b n) : a * (a * b) * a = (a * b)⁻¹ := by
  have hinv : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, h.inv_a, h.inv_b]
  rw [hinv, ← mul_assoc, h.mul_self_a, one_mul]

theorem IsDihedralGen.conj_mem (h : IsDihedralGen a b n) {y : W}
    (hy : y ∈ Subgroup.zpowers (a * b)) : a * y * a ∈ Subgroup.zpowers (a * b) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have e : a * (a * b) ^ k * a = ((a * b)⁻¹) ^ k := by
    rw [← h.a_mul_r_mul_a]
    have := map_zpow (MulAut.conj a) (a * b) k
    simpa [MulAut.conj_apply, h.inv_a] using this
  rw [e]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k

theorem IsDihedralGen.cover (h : IsDihedralGen a b n) (w : W) :
    w ∈ Subgroup.zpowers (a * b) ∨ w * a ∈ Subgroup.zpowers (a * b) := by
  have hA := h.mul_mul_a
  have hw : w ∈ Subgroup.closure ({a, b} : Set W) := by rw [h.closure_eq]; trivial
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · right; rw [h.mul_self_a]; exact Subgroup.one_mem _
    · right
      have : x * a = (a * x)⁻¹ := by rw [mul_inv_rev, h.inv_a, h.inv_b]
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  | one => left; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    rcases ihx with hx' | hx' <;> rcases ihy with hy' | hy'
    · left; exact Subgroup.mul_mem _ hx' hy'
    · right
      have : x * y * a = x * (y * a) := by rw [mul_assoc]
      rw [this]; exact Subgroup.mul_mem _ hx' hy'
    · right
      have : x * y * a = (x * a) * (a * y * a) := by
        simp only [mul_assoc, hA]
      rw [this]; exact Subgroup.mul_mem _ hx' (h.conj_mem hy')
    · left
      have : x * y = (x * a) * (a * (y * a) * a) := by
        simp only [mul_assoc, hA, h.mul_self_a, mul_one]
      rw [this]; exact Subgroup.mul_mem _ hx' (h.conj_mem hy')
  | inv x hx ihx =>
    rcases ihx with hx' | hx'
    · left; exact Subgroup.inv_mem _ hx'
    · right
      have : x⁻¹ * a = a * (x * a)⁻¹ * a := by
        simp only [mul_inv_rev, h.inv_a, hA]
      rw [this]; exact h.conj_mem (Subgroup.inv_mem _ hx')

theorem IsDihedralGen.a_not_mem (h : IsDihedralGen a b n) : a ∉ Subgroup.zpowers (a * b) := by
  intro ha
  set r := a * b with hr
  have hb : b ∈ Subgroup.zpowers r := by
    have : b = a * r := by rw [hr, h.mul_mul_a]
    rw [this]; exact Subgroup.mul_mem _ ha (Subgroup.mem_zpowers _)
  have hall : ∀ w : W, w ∈ Subgroup.zpowers r := by
    intro w
    have hw : w ∈ Subgroup.closure ({a, b} : Set W) := by rw [h.closure_eq]; trivial
    refine (Subgroup.closure_le _).2 ?_ hw
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hcomm : a * b = b * a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]
  have hr2 : r * r = 1 := by
    have : r⁻¹ = r := by
      rw [hr, mul_inv_rev, h.inv_a, h.inv_b, ← hcomm]
    calc r * r = r * r⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel r
  have htop : Subgroup.zpowers r = ⊤ := (Subgroup.eq_top_iff' _).2 hall
  have hcard : Nat.card W ≤ 2 := by
    have h1 : Nat.card (Subgroup.zpowers r) ≤ 2 := by
      rw [Nat.card_zpowers]
      have : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hr2)
      exact Nat.le_of_dvd (by norm_num) this
    have h2 : Nat.card W = Nat.card (Subgroup.zpowers r) := by
      rw [htop, Subgroup.card_top]
    omega
  have := h.card_eq
  have := h.three_le
  omega

theorem IsDihedralGen.orderOf_mul (h : IsDihedralGen a b n) : orderOf (a * b) = n := by
  have hidx : (Subgroup.zpowers (a * b)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨a, fun w => ?_⟩
    rcases h.cover w with hw | hw
    · refine Or.inr ⟨hw, fun hwa => h.a_not_mem ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) hwa
      simpa using this
    · refine Or.inl ⟨hw, fun hw' => h.a_not_mem ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hw') hw
      simpa using this
  have := Subgroup.card_mul_index (Subgroup.zpowers (a * b))
  rw [hidx, Nat.card_zpowers, h.card_eq] at this
  omega

theorem IsDihedralGen.pow_eq_one (h : IsDihedralGen a b n) : (a * b) ^ n = 1 := by
  rw [← h.orderOf_mul]
  exact pow_orderOf_eq_one _

theorem IsDihedralGen.altWord_eq (h : IsDihedralGen a b n) : altWord a b n = altWord b a n := by
  have hpow := h.pow_eq_one
  have hinv : b * a = (a * b)⁻¹ := by rw [mul_inv_rev, h.inv_a, h.inv_b]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [altWord_two_mul, altWord_two_mul, hinv, inv_pow]
    have h2 : (a * b) ^ k * (a * b) ^ k = 1 := by rw [← pow_add, ← two_mul]; exact hpow
    exact (inv_eq_of_mul_eq_one_right h2)
  · rw [altWord_two_mul_add_one, altWord_two_mul_add_one, hinv, inv_pow]
    have h1 : ((a * b) ^ k)⁻¹ = (a * b) ^ (k + 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add]
      have : k + (k + 1) = 2 * k + 1 := by ring
      rw [this]; exact hpow
    rw [h1, pow_succ', mul_assoc a b, h.mul_mul_a]

section Generic

variable {x y : W} {n : ℕ}

theorem exists_mul_altWord (hx : x * x = 1) (hy : y * y = 1)
    (hbraid : altWord x y n = altWord y x n) (hn : 1 ≤ n) {t : ℕ} (ht : t ≤ n) {s : W}
    (hs : s = x ∨ s = y) :
    ∃ j, j ≤ n ∧ j ≤ t + 1 ∧
      (s * altWord x y t = altWord x y j ∨ s * altWord x y t = altWord y x j) := by
  have hn1 : n - 1 + 1 = n := by omega
  have hlast := altWord_succ_left y x (n - 1)
  rw [hn1] at hlast
  rcases hs with rfl | rfl
  · by_cases hev : Even t
    · by_cases htn : t = n
      · subst htn
        refine ⟨t - 1, by omega, by omega, Or.inr ?_⟩
        have hodd : ¬ Even (t - 1) := by
          intro h'
          obtain ⟨k, hk⟩ := hev
          obtain ⟨l, hl⟩ := h'
          omega
        rw [hbraid, hlast]
        simp [hodd, ← mul_assoc, hx]
      · exact ⟨t + 1, by omega, le_refl _, Or.inl (mul_altWord_even t hev)⟩
    · exact ⟨t - 1, by omega, by omega, Or.inl (mul_altWord_odd' hx t hev)⟩
  · by_cases hev : Even t
    · by_cases ht0 : t = 0
      · subst ht0
        refine ⟨1, hn, le_refl _, Or.inr ?_⟩
        simp [altWord_zero, altWord_one]
      · exact ⟨t - 1, by omega, by omega, Or.inl (mul_altWord_even' hy t hev ht0)⟩
    · by_cases htn : t = n
      · subst htn
        refine ⟨t - 1, by omega, by omega, Or.inr ?_⟩
        have heven : Even (t - 1) := by
          have : ¬ Even t := hev
          rw [Nat.even_sub (by omega)]
          simpa using this
        rw [hbraid, hlast]
        simp [heven, ← mul_assoc, hy]
      · exact ⟨t + 1, by omega, le_refl _, Or.inl (mul_altWord_odd t hev)⟩

end Generic

section Structure

variable {a b : W} {n : ℕ}

theorem IsDihedralGen.symm (h : IsDihedralGen a b n) : IsDihedralGen b a n where
  mul_self_a := h.mul_self_b
  mul_self_b := h.mul_self_a
  ne := h.ne.symm
  closure_eq := by rw [Set.pair_comm]; exact h.closure_eq
  card_eq := h.card_eq
  three_le := h.three_le

theorem IsDihedralGen.exists_altWord_of_list (h : IsDihedralGen a b n) (l : List W)
    (hl : ∀ s ∈ l, s = a ∨ s = b) :
    ∃ t, t ≤ n ∧ t ≤ l.length ∧ (l.prod = altWord a b t ∨ l.prod = altWord b a t) := by
  have hn1 : 1 ≤ n := by have := h.three_le; omega
  induction l with
  | nil => exact ⟨0, by omega, le_refl _, Or.inl (by simp [altWord_zero])⟩
  | cons s l ih =>
    obtain ⟨t, htn, htl, ht⟩ := ih (fun s' hs' => hl s' (by simp [hs']))
    have hs := hl s (by simp)
    rcases ht with ht | ht
    · obtain ⟨j, hj, hjt, hj'⟩ := exists_mul_altWord h.mul_self_a h.mul_self_b h.altWord_eq hn1
        htn hs
      refine ⟨j, hj, by simp only [List.length_cons]; omega, ?_⟩
      rw [List.prod_cons, ht]
      exact hj'
    · obtain ⟨j, hj, hjt, hj'⟩ := exists_mul_altWord (x := b) (y := a) h.mul_self_b h.mul_self_a
        h.altWord_eq.symm hn1 htn hs.symm
      refine ⟨j, hj, by simp only [List.length_cons]; omega, ?_⟩
      rw [List.prod_cons, ht]
      exact hj'.symm

theorem IsDihedralGen.exists_altWord (h : IsDihedralGen a b n) (w : W) :
    ∃ t, t ≤ n ∧ (w = altWord a b t ∨ w = altWord b a t) := by
  have hw : w ∈ Subgroup.closure ({a, b} : Set W) := by rw [h.closure_eq]; trivial
  have hJ : ∀ s ∈ ({a, b} : Set W), s * s = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact h.mul_self_a
    · exact h.mul_self_b
  obtain ⟨l, hl, rfl⟩ := (mem_closure_iff_exists_list hJ).1 hw
  obtain ⟨t, htn, -, ht⟩ := h.exists_altWord_of_list l (fun s hs => by simpa using hl s hs)
  exact ⟨t, htn, ht⟩

def altParam (a b : W) (n : ℕ) : Fin (n + 1) ⊕ Fin (n - 1) → W
  | Sum.inl i => altWord a b i
  | Sum.inr j => altWord b a (j + 1)

theorem IsDihedralGen.altParam_bijective (h : IsDihedralGen a b n) :
    Function.Bijective (altParam a b n) := by
  have hfin : Finite W := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; have := h.three_le; omega)
  have hsurj : Function.Surjective (altParam a b n) := by
    intro w
    obtain ⟨t, htn, ht | ht⟩ := h.exists_altWord w
    · exact ⟨Sum.inl ⟨t, by omega⟩, ht.symm⟩
    · by_cases ht0 : t = 0
      · subst ht0
        exact ⟨Sum.inl 0, by simpa [altParam, altWord_zero] using ht.symm⟩
      by_cases htn' : t = n
      · subst htn'
        exact ⟨Sum.inl ⟨t, by omega⟩, by simpa [altParam] using (ht.trans h.altWord_eq.symm).symm⟩
      · exact ⟨Sum.inr ⟨t - 1, by omega⟩, by
          simp only [altParam]
          rw [show t - 1 + 1 = t by omega]
          exact ht.symm⟩
  refine hsurj.bijective_of_nat_card_le ?_
  rw [Nat.card_sum, h.card_eq]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  have := h.three_le
  omega

theorem IsDihedralGen.altWord_inj (h : IsDihedralGen a b n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (e : altWord a b i = altWord a b j) : i = j := by
  have := h.altParam_bijective.1 (a₁ := Sum.inl ⟨i, by omega⟩) (a₂ := Sum.inl ⟨j, by omega⟩) e
  simpa using this

theorem IsDihedralGen.altWord_ne (h : IsDihedralGen a b n) {i j : ℕ} (hi : i ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n) : altWord a b i ≠ altWord b a j := by
  intro e
  have := h.altParam_bijective.1 (a₁ := Sum.inl ⟨i, by omega⟩)
    (a₂ := Sum.inr ⟨j - 1, by omega⟩) (by simpa [altParam, show j - 1 + 1 = j by omega] using e)
  simp at this

theorem IsDihedralGen.altWord_eq_swap (h : IsDihedralGen a b n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (e : altWord a b i = altWord b a j) : (i = 0 ∧ j = 0) ∨ (i = n ∧ j = n) := by
  by_cases hj0 : j = 0
  · subst hj0
    have e' : altWord a b i = altWord a b 0 := by rw [e]; rfl
    exact Or.inl ⟨h.altWord_inj hi (Nat.zero_le _) e', rfl⟩
  by_cases hjn : j = n
  · subst hjn
    exact Or.inr ⟨h.altWord_inj hi hj (e.trans h.altWord_eq.symm), rfl⟩
  · exact absurd e (h.altWord_ne hi (Nat.one_le_iff_ne_zero.2 hj0) (by omega))

end Structure

section WordLength

variable {a b : W} {n : ℕ}

def altList (a b : W) : ℕ → List W
  | 0 => []
  | i + 1 => altList b a i ++ [a]

theorem altList_prod (a b : W) (i : ℕ) : (altList a b i).prod = altWord a b i := by
  induction i generalizing a b with
  | zero => rfl
  | succ i ih => rw [altList, List.prod_append, ih, altWord_succ]; simp

omit [Group W] in
theorem altList_length (a b : W) (i : ℕ) : (altList a b i).length = i := by
  induction i generalizing a b with
  | zero => rfl
  | succ i ih => rw [altList, List.length_append, ih]; rfl

omit [Group W] in
theorem mem_altList {a b s : W} {i : ℕ} (hs : s ∈ altList a b i) : s = a ∨ s = b := by
  induction i generalizing a b with
  | zero => simp [altList] at hs
  | succ i ih =>
    rw [altList, List.mem_append] at hs
    rcases hs with hs | hs
    · exact (ih hs).symm
    · left; simpa using hs

theorem wordLength_altWord_le (a b : W) (i : ℕ) :
    wordLength ({a, b} : Set W) (altWord a b i) ≤ i := by
  have := wordLength_le (J := ({a, b} : Set W)) (l := altList a b i) (fun s hs => by
    rcases mem_altList hs with rfl | rfl <;> simp)
  rwa [altList_prod, altList_length] at this

theorem IsDihedralGen.wordLength_altWord (h : IsDihedralGen a b n) {i : ℕ} (hi : i ≤ n) :
    wordLength ({a, b} : Set W) (altWord a b i) = i := by
  refine le_antisymm (wordLength_altWord_le a b i) ?_
  have hJ : ∀ s ∈ ({a, b} : Set W), s * s = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact h.mul_self_a
    · exact h.mul_self_b
  have hw : altWord a b i ∈ Subgroup.closure ({a, b} : Set W) := by
    rw [h.closure_eq]; trivial
  obtain ⟨l, hl, hlen, hprod⟩ := exists_list_length_eq_wordLength hJ hw
  obtain ⟨t, htn, htl, ht⟩ := h.exists_altWord_of_list l (fun s hs => by simpa using hl s hs)
  rw [hprod] at ht
  rcases ht with ht | ht
  · have := h.altWord_inj hi htn ht
    omega
  · rcases h.altWord_eq_swap hi htn ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem IsDihedralGen.wordLength_altWord' (h : IsDihedralGen a b n) {i : ℕ} (hi : i ≤ n) :
    wordLength ({a, b} : Set W) (altWord b a i) = i := by
  have := h.symm.wordLength_altWord hi
  rwa [Set.pair_comm] at this

theorem IsDihedralGen.wordLength_le (h : IsDihedralGen a b n) (w : W) :
    wordLength ({a, b} : Set W) w ≤ n := by
  obtain ⟨t, htn, ht | ht⟩ := h.exists_altWord w
  · rw [ht, h.wordLength_altWord htn]; exact htn
  · rw [ht, h.wordLength_altWord' htn]; exact htn

theorem IsDihedralGen.wordLength_gen_mul_longest (h : IsDihedralGen a b n) {s : W}
    (hs : s = a ∨ s = b) : wordLength ({a, b} : Set W) (s * altWord a b n) + 1 = n := by
  have hn := h.three_le
  have hbr := h.altWord_eq
  have key : ∃ j, j + 1 = n ∧ (s * altWord a b n = altWord a b j ∨ s * altWord a b n = altWord b a j) := by
    refine ⟨n - 1, by omega, ?_⟩
    rcases hs with rfl | rfl
    · by_cases hev : Even n
      · right
        rw [hbr]
        exact mul_altWord_even' h.mul_self_a n hev (by omega)
      · left
        exact mul_altWord_odd' h.mul_self_a n hev
    · by_cases hev : Even n
      · left
        exact mul_altWord_even' h.mul_self_b n hev (by omega)
      · right
        rw [hbr]
        exact mul_altWord_odd' h.mul_self_b n hev
  obtain ⟨j, hj, hj'⟩ := key
  rcases hj' with e | e
  · rw [e, h.wordLength_altWord (by omega)]; exact hj
  · rw [e, h.wordLength_altWord' (by omega)]; exact hj

end WordLength

end Dihedral

end CFSG.GH74.BNPair
