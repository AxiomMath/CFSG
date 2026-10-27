module

import all Init.Data.Array.QSort.Basic

public section

namespace CFSG.KC.QSort

universe u

variable {α : Type u} {n : Nat}

structure RangePerm (lo hi : Nat) (as bs : Vector α n) : Prop where
  perm : bs.Perm as
  out : ∀ k (hk : k < n), k < lo ∨ hi < k → bs[k] = as[k]
  src : ∀ k (hk : k < n), lo ≤ k → k ≤ hi →
    ∃ k' : Nat, ∃ hk' : k' < n, lo ≤ k' ∧ k' ≤ hi ∧ bs[k] = as[k']

namespace RangePerm

variable {lo hi : Nat}

theorem refl (as : Vector α n) : RangePerm lo hi as as :=
  ⟨Vector.Perm.refl as, fun _ _ _ => rfl, fun k hk h1 h2 => ⟨k, hk, h1, h2, rfl⟩⟩

theorem trans {as bs cs : Vector α n} (h₁ : RangePerm lo hi as bs) (h₂ : RangePerm lo hi bs cs) :
    RangePerm lo hi as cs where
  perm := h₂.perm.trans h₁.perm
  out k hk h := (h₂.out k hk h).trans (h₁.out k hk h)
  src k hk h1 h2 := by
    obtain ⟨k', hk', a1, a2, e⟩ := h₂.src k hk h1 h2
    obtain ⟨k'', hk'', b1, b2, e'⟩ := h₁.src k' hk' a1 a2
    exact ⟨k'', hk'', b1, b2, e.trans e'⟩

theorem mono {lo' hi' : Nat} {as bs : Vector α n} (hl : lo ≤ lo') (hh : hi' ≤ hi)
    (h : RangePerm lo' hi' as bs) : RangePerm lo hi as bs where
  perm := h.perm
  out k hk hk' := h.out k hk (by omega)
  src k hk h1 h2 := by
    by_cases hin : lo' ≤ k ∧ k ≤ hi'
    · obtain ⟨k', hk', a1, a2, e⟩ := h.src k hk hin.1 hin.2
      exact ⟨k', hk', by omega, by omega, e⟩
    · exact ⟨k, hk, h1, h2, h.out k hk (by omega)⟩

theorem swap (as : Vector α n) {i j : Nat} (hin : i < n) (hjn : j < n) (h1 : lo ≤ i)
    (h2 : i ≤ hi) (h3 : lo ≤ j) (h4 : j ≤ hi) : RangePerm lo hi as (as.swap i j hin hjn) where
  perm := Vector.swap_perm hin hjn
  out k hk hk' := by
    rw [Vector.getElem_swap, ite_eq_right (by omega), ite_eq_right (by omega)]
  src k hk k1 k2 := by
    rw [Vector.getElem_swap]
    by_cases e1 : k = i
    · rw [ite_eq_left e1]
      exact ⟨j, hjn, h3, h4, rfl⟩
    · rw [ite_eq_right e1]
      by_cases e2 : k = j
      · rw [ite_eq_left e2]
        exact ⟨i, hin, h1, h2, rfl⟩
      · rw [ite_eq_right e2]
        exact ⟨k, hk, k1, k2, rfl⟩

theorem ite_swap (as : Vector α n) (c : Prop) [Decidable c] {i j : Nat} (hin : i < n) (hjn : j < n)
    (h1 : lo ≤ i) (h2 : i ≤ hi) (h3 : lo ≤ j) (h4 : j ≤ hi) :
    RangePerm lo hi as (if c then as.swap i j hin hjn else as) := by
  split
  · exact swap as hin hjn h1 h2 h3 h4
  · exact refl as

end RangePerm

private theorem loop_range (lt : α → α → Bool) (lo hi : Nat) (hhi : hi < n) (pivot : α) :
    ∀ (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi),
      RangePerm lo hi as (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2 := by
  intro as i k ilo ik w
  induction as, i, k, ilo, ik, w using Array.qpartition.loop.induct lt lo hi hhi pivot with
  | case1 as i k ilo ik w h hlt ih =>
    rw [Array.qpartition.loop, dite_eq_left h, ite_eq_left hlt]
    exact (RangePerm.swap as _ _ ilo (by omega) (by omega) (by omega)).trans ih
  | case2 as i k ilo ik w h hlt ih =>
    rw [Array.qpartition.loop, dite_eq_left h, ite_eq_right hlt]
    exact ih
  | case3 as i k ilo ik w h =>
    rw [Array.qpartition.loop, dite_eq_right h]
    exact RangePerm.swap as (by omega) hhi ilo (by omega) (by omega) (by omega)

theorem qpartition_range (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat) (w : lo ≤ hi)
    (hlo : lo < n) (hhi : hi < n) :
    RangePerm lo hi as (Array.qpartition as lt lo hi w hlo hhi).2 := by
  unfold Array.qpartition
  dsimp only
  refine (RangePerm.ite_swap _ _ _ _ (by omega) (by omega) (by omega) (by omega)).trans
    ((RangePerm.ite_swap _ _ _ _ (by omega) (by omega) (by omega) (by omega)).trans
      ((RangePerm.ite_swap _ _ _ _ (by omega) (by omega) (by omega) (by omega)).trans
        (loop_range _ _ _ _ _ _ _ _ _ _ _)))
  all_goals omega

structure PartSpec (lt : α → α → Bool) (lo hi : Nat) (as bs : Vector α n) (m : Nat) : Prop where
  range : RangePerm lo hi as bs
  lo_le : lo ≤ m
  lt_hi : m < hi
  hmn : m < n
  left : ∀ j (hj : j < n), lo ≤ j → j < m → lt bs[j] (bs[m]'hmn) = true
  right : ∀ j (hj : j < n), m < j → j ≤ hi → lt bs[j] (bs[m]'hmn) = false

private theorem loop_spec (lt : α → α → Bool) (lo hi : Nat) (hhi : hi < n) (pivot : α)
    (as₀ : Vector α n) (mid : Nat) (hm1 : lo ≤ mid) (hm2 : mid < hi)
    (hmv : lt (as₀[mid]'(by omega)) pivot = false) :
    ∀ (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi),
      RangePerm lo hi as₀ as →
      (∀ j (hj : j < n), lo ≤ j → j < i → lt as[j] pivot = true) →
      (∀ j (hj : j < n), i ≤ j → j < k → lt as[j] pivot = false) →
      as[hi] = pivot →
      (k ≤ mid → as[mid]'(by omega) = as₀[mid]'(by omega)) →
      (mid < k → i < k) →
      PartSpec lt lo hi as₀ (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2
        (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).1.1 := by
  intro as i k ilo ik w
  induction as, i, k, ilo, ik, w using Array.qpartition.loop.induct lt lo hi hhi pivot with
  | case1 as i k ilo ik w h hlt ih =>
    intro hR hI1 hI2 hH hM hK
    rw [Array.qpartition.loop, dite_eq_left h, ite_eq_left hlt]
    refine ih (hR.trans (RangePerm.swap as _ _ ilo (by omega) (by omega) (by omega)))
      (fun j hj j1 j2 => ?_) (fun j hj j1 j2 => ?_) ?_ (fun hk => ?_) (fun hk => ?_)
    · rw [Vector.getElem_swap]
      by_cases e : j = i
      · rw [ite_eq_left e]
        exact hlt
      · rw [ite_eq_right e, ite_eq_right (by omega)]
        exact hI1 j hj j1 (by omega)
    · rw [Vector.getElem_swap, ite_eq_right (by omega)]
      by_cases e : j = k
      · rw [ite_eq_left e]
        exact hI2 i (by omega) (Nat.le_refl _) (by omega)
      · rw [ite_eq_right e]
        exact hI2 j hj (by omega) (by omega)
    · rw [Vector.getElem_swap, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hH
    · rw [Vector.getElem_swap, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hM (by omega)
    · by_cases e : mid < k
      · have := hK e
        omega
      · have hkm : k = mid := by omega
        subst hkm
        rw [hM (Nat.le_refl _)] at hlt
        rw [hmv] at hlt
        exact absurd hlt (by simp)
  | case2 as i k ilo ik w h hlt ih =>
    intro hR hI1 hI2 hH hM hK
    rw [Array.qpartition.loop, dite_eq_left h, ite_eq_right hlt]
    refine ih hR hI1 (fun j hj j1 j2 => ?_) hH (fun hk => hM (by omega)) (fun _ => by omega)
    by_cases e : j = k
    · subst e
      simpa using hlt
    · exact hI2 j hj j1 (by omega)
  | case3 as i k ilo ik w h =>
    intro hR hI1 hI2 hH hM hK
    rw [Array.qpartition.loop, dite_eq_right h]
    dsimp only
    have hk : k = hi := by omega
    subst hk
    have hi' : i < k := hK hm2
    have hpiv : (as.swap i k (by omega) hhi)[i]'(by omega) = pivot := by
      rw [Vector.getElem_swap, ite_eq_left rfl]
      exact hH
    refine ⟨hR.trans (RangePerm.swap as _ _ ilo (by omega) (by omega) (by omega)), ilo, hi',
      by omega, fun j hj j1 j2 => ?_, fun j hj j1 j2 => ?_⟩
    · rw [hpiv, Vector.getElem_swap, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hI1 j hj j1 j2
    · rw [hpiv, Vector.getElem_swap, ite_eq_right (by omega)]
      by_cases e : j = k
      · rw [ite_eq_left e]
        exact hI2 i (by omega) (Nat.le_refl _) hi'
      · rw [ite_eq_right e]
        exact hI2 j hj (by omega) (by omega)

theorem median_not_lt (lt : α → α → Bool) (hasymm : ∀ a b, lt a b = true → lt b a = false)
    (as : Vector α n) (mid hi : Nat) (hm : mid < n) (hh : hi < n) (hne : mid ≠ hi) :
    lt ((if lt as[mid] as[hi] = true then as.swap mid hi hm hh else as)[mid])
      ((if lt as[mid] as[hi] = true then as.swap mid hi hm hh else as)[hi]) = false := by
  by_cases h : lt as[mid] as[hi] = true
  · simp only [h, ite_true]
    rw [Vector.getElem_swap, ite_eq_left rfl, Vector.getElem_swap, ite_eq_right (Ne.symm hne), ite_eq_left rfl]
    exact hasymm _ _ h
  · simp only [h]
    simpa using h

theorem qpartition_spec (lt : α → α → Bool) (hasymm : ∀ a b, lt a b = true → lt b a = false)
    (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (h : lo < hi) :
    PartSpec lt lo hi as (Array.qpartition as lt lo hi w hlo hhi).2
      (Array.qpartition as lt lo hi w hlo hhi).1.1 := by
  have hm1 : lo ≤ (lo + hi) / 2 := by omega
  have hm2 : (lo + hi) / 2 < hi := by omega
  have key : ∀ A3 : Vector α n, RangePerm lo hi as A3 →
      lt (A3[(lo + hi) / 2]'(by omega)) A3[hi] = false →
      PartSpec lt lo hi as (Array.qpartition.loop lt lo hi hhi A3[hi] A3 lo lo (Nat.le_refl _) (Nat.le_refl _) w).2
        (Array.qpartition.loop lt lo hi hhi A3[hi] A3 lo lo (Nat.le_refl _) (Nat.le_refl _) w).1.1 := by
    intro A3 hR hmv
    have := loop_spec lt lo hi hhi A3[hi] A3 _ hm1 hm2 hmv A3 lo lo (Nat.le_refl _) (Nat.le_refl _) w
      (RangePerm.refl A3) (fun j _ j1 j2 => by omega) (fun j _ j1 j2 => by omega) rfl
      (fun _ => rfl) (fun e => by omega)
    exact ⟨hR.trans this.range, this.lo_le, this.lt_hi, this.hmn, this.left, this.right⟩
  unfold Array.qpartition
  dsimp only
  refine key _ ?_ (median_not_lt lt hasymm _ _ _ _ _ (by omega))
  exact (RangePerm.ite_swap _ _ _ _ (by omega) (by omega) (by omega) (by omega)).trans
    ((RangePerm.ite_swap _ _ _ _ (by omega) (by omega) (by omega) (by omega)).trans
      (RangePerm.ite_swap _ _ _ _ (by omega) (by omega) (by omega) (by omega)))

private theorem sort_range (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi)
    (hlo : lo < n) (hhi : hi < n) :
    RangePerm lo hi as (Array.qsort.sort lt as lo hi w hlo hhi) := by
  induction as, lo, hi, w, hlo, hhi using Array.qsort.sort.induct lt with
  | case1 as lo hi w hlo hhi h mid hmid as₁ hp h₂ =>
    rw [Array.qsort.sort, dite_eq_left h, hp]
    dsimp only
    rw [dite_eq_left h₂]
    have := qpartition_range as lt lo hi w hlo hhi
    rw [hp] at this
    exact this
  | case2 as lo hi w hlo hhi h mid hmid as₁ hp h₂ ih₁ _ ih₂ =>
    rw [Array.qsort.sort, dite_eq_left h, hp]
    dsimp only
    rw [dite_eq_right h₂]
    have := qpartition_range as lt lo hi w hlo hhi
    rw [hp] at this
    exact this.trans ((ih₁.mono (Nat.le_refl _) hmid.2).trans (ih₂.mono (by omega) (Nat.le_refl _)))
  | case3 as lo hi w hlo hhi h =>
    rw [Array.qsort.sort, dite_eq_right h]
    exact RangePerm.refl as

private theorem sort_sorted (lt : α → α → Bool) (htrans : ∀ a b c, lt a b = true → lt b c = true →
    lt a c = true) (hasymm : ∀ a b, lt a b = true → lt b a = false) (as : Vector α n)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    ∀ i j, lo ≤ i → (hij : i < j) → (hj : j ≤ hi) →
      lt (Array.qsort.sort lt as lo hi w hlo hhi)[j] (Array.qsort.sort lt as lo hi w hlo hhi)[i]
        = false := by
  induction as, lo, hi, w, hlo, hhi using Array.qsort.sort.induct lt with
  | case1 as lo hi w hlo hhi h mid hmid as₁ hp h₂ =>
    have := qpartition_spec lt hasymm as lo hi w hlo hhi h
    rw [hp] at this
    exact absurd this.lt_hi (by simpa using h₂)
  | case2 as lo hi w hlo hhi h mid hmid as₁ hp h₂ ih₁ _ ih₂ =>
    intro i j hi' hij hj
    rw [Array.qsort.sort, dite_eq_left h, hp]
    dsimp only
    rw [dite_eq_right h₂]
    have hP := qpartition_spec lt hasymm as lo hi w hlo hhi h
    rw [hp] at hP
    dsimp only at hP
    have hR₁ := sort_range lt as₁ lo mid (by omega) hlo (by omega)
    have hR₂ := sort_range lt (Array.qsort.sort lt as₁ lo mid (by omega) hlo (by omega)) (mid + 1)
      hi (by omega) (by omega) hhi
    by_cases hjm : mid < j
    · by_cases him : mid < i
      · exact ih₂ i j (by omega) hij hj
      ·
        rw [hR₂.out i (by omega) (Or.inl (by omega))]
        obtain ⟨i', hi'n, i1, i2, ei⟩ := hR₁.src i (by omega) hi' (by omega)
        obtain ⟨j', hj'n, j1, j2, ej⟩ := hR₂.src j (by omega) (by omega) hj
        rw [ei, ej, hR₁.out j' hj'n (Or.inr (by omega))]
        have hr := hP.right j' hj'n (by omega) j2
        by_cases e : i' = mid
        · subst e
          exact hr
        · have hl := hP.left i' hi'n i1 (by omega)
          cases hc : lt as₁[j'] as₁[i']
          · rfl
          · rw [htrans _ _ _ hc hl] at hr
            exact absurd hr (by simp)
    · rw [hR₂.out i (by omega) (Or.inl (by omega)), hR₂.out j (by omega) (Or.inl (by omega))]
      exact ih₁ i j hi' hij (by omega)
  | case3 as lo hi w hlo hhi h =>
    intro i j hi' hij hj
    omega

private theorem qsort_eq (as : Array α) (lt : α → α → Bool) (h : as.size ≠ 0) :
    as.qsort lt = (Array.qsort.sort lt as.toVector 0 (as.size - 1) (by omega) (by omega)
      (by omega)).toArray := by
  unfold Array.qsort
  rw [dite_eq_right h]
  have e1 : min 0 (as.size - 1) = 0 := by omega
  have e2 : max 0 (min (as.size - 1) (as.size - 1)) = as.size - 1 := by omega
  simp only [e1, e2]

theorem qsort_size (as : Array α) (lt : α → α → Bool) : (as.qsort lt).size = as.size := by
  by_cases h : as.size = 0
  · unfold Array.qsort
    rw [dite_eq_left h]
  · rw [qsort_eq as lt h]
    simp

theorem qsort_perm (as : Array α) (lt : α → α → Bool) : (as.qsort lt).Perm as := by
  by_cases h : as.size = 0
  · unfold Array.qsort
    rw [dite_eq_left h]
  · rw [qsort_eq as lt h]
    have := (sort_range lt as.toVector 0 (as.size - 1) (by omega) (by omega) (by omega)).perm
    have h2 := Vector.perm_iff_toArray_perm.1 this
    simpa using h2

theorem qsort_sorted (as : Array α) (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) (i j : Nat) (hij : i < j)
    (hj : j < (as.qsort lt).size) : lt (as.qsort lt)[j] ((as.qsort lt)[i]'(by omega)) = false := by
  have h : as.size ≠ 0 := by rw [qsort_size] at hj; omega
  have hj' : j < as.size := by rw [qsort_size] at hj; exact hj
  have := sort_sorted lt htrans hasymm as.toVector 0 (as.size - 1) (by omega) (by omega)
    (by omega) i j (Nat.zero_le _) hij (by omega)
  simp only [qsort_eq as lt h, Vector.getElem_toArray]
  exact this

theorem qsort_pairwise (as : Array α) (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) :
    (as.qsort lt).toList.Pairwise fun a b => lt b a = false := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [Array.getElem_toList]
  exact qsort_sorted as lt htrans hasymm i j hij (by simpa using hj)

end CFSG.KC.QSort
