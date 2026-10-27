module

public import Mathlib.Data.Finset.Sort

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

structure Enumeration (S : Finset ℕ) (a : ℕ → ℕ) : Prop where
  zero : a 0 = 0
  lt : ∀ k, k < S.card → a k < a (k + 1)
  mem : ∀ k, 1 ≤ k → k ≤ S.card → a k ∈ S
  surj : ∀ i ∈ S, ∃ k, 1 ≤ k ∧ k ≤ S.card ∧ a k = i

theorem exists_enumeration (S : Finset ℕ) (hS : ∀ i ∈ S, 1 ≤ i) : ∃ a, Enumeration S a := by
  classical
  let e := S.orderEmbOfFin rfl
  let a : ℕ → ℕ := fun k =>
    if h : 0 < k ∧ 0 < S.card then e ⟨min k S.card - 1, by omega⟩ else 0
  have ha : ∀ k (hk1 : 1 ≤ k) (hk2 : k ≤ S.card), a k = e ⟨k - 1, by omega⟩ := by
    intro k hk1 hk2
    have h : 0 < k ∧ 0 < S.card := ⟨by omega, by omega⟩
    simp only [a, h, and_self, dite_true]
    congr 2
    omega
  refine ⟨a, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp [a]
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have h0 : a 0 = 0 := by simp [a]
      have h1 : a 1 ∈ S := by
        rw [ha 1 le_rfl (by omega)]
        exact S.orderEmbOfFin_mem rfl _
      have := hS _ h1
      show a 0 < a 1
      omega
    · rw [ha k hk0 hk.le, ha (k + 1) (by omega) (by omega)]
      exact e.strictMono (by simp [Fin.lt_def]; omega)
  · intro k hk1 hk2
    rw [ha k hk1 hk2]
    exact S.orderEmbOfFin_mem rfl _
  · intro i hi
    have : i ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hi
    obtain ⟨j, rfl⟩ := this
    refine ⟨j.val + 1, by omega, by omega, ?_⟩
    rw [ha _ (by omega) (by omega)]
    congr 2

variable {S : Finset ℕ} {a : ℕ → ℕ}

namespace Enumeration

theorem strictMonoOn (ha : Enumeration S a) {k k' : ℕ} (hk : k < k') (hk' : k' ≤ S.card) :
    a k < a k' := by
  induction k' with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · exact (ih h (by omega)).trans (ha.lt m (by omega))
    · exact ha.lt _ (by omega)

theorem lt_iff (ha : Enumeration S a) {k k' : ℕ} (hk : k ≤ S.card) (hk' : k' ≤ S.card) :
    a k < a k' ↔ k < k' := by
  constructor
  · intro h
    by_contra hc
    rcases (not_lt.mp hc).eq_or_lt with rfl | h2
    · omega
    · exact absurd (ha.strictMonoOn h2 hk) (by omega)
  · intro h
    exact ha.strictMonoOn h hk'

theorem not_mem_between (ha : Enumeration S a) {k : ℕ} (hk : k < S.card) {x : ℕ}
    (h1 : a k < x) (h2 : x < a (k + 1)) : x ∉ S := by
  intro hx
  obtain ⟨m, hm1, hm2, rfl⟩ := ha.surj x hx
  have h3 := (ha.lt_iff (by omega) hm2).mp h1
  have h4 := (ha.lt_iff hm2 (by omega : k + 1 ≤ S.card)).mp h2
  omega

theorem le_last (ha : Enumeration S a) {x : ℕ} (hx : x ∈ S) : x ≤ a S.card := by
  obtain ⟨m, hm1, hm2, rfl⟩ := ha.surj x hx
  rcases hm2.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (ha.strictMonoOn h le_rfl).le

theorem last_mem (ha : Enumeration S a) (hne : S.Nonempty) : a S.card ∈ S :=
  ha.mem _ (Finset.card_pos.mpr hne) le_rfl

end Enumeration

section Gaps

variable {r : ℕ}

theorem gap_le_two (ha : Enumeration S a) (hS : ∀ i ∈ S, i ≤ r)
    (hshort : ∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → j₂ < r → j₁ ∉ S → j₂ ∉ S → False)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ S.card) : a k ≤ a (k - 1) + 2 := by
  by_contra hc
  have hlt : a (k - 1) < a k := ha.strictMonoOn (by omega) hk2
  have hr : a k ≤ r := hS _ (ha.mem k hk1 hk2)
  have h1 : a (k - 1) + 1 ∉ S := ha.not_mem_between (k := k - 1) (by omega) (by omega)
    (by rw [Nat.sub_add_cancel hk1]; omega)
  have h2 : a (k - 1) + 2 ∉ S := ha.not_mem_between (k := k - 1) (by omega) (by omega)
    (by rw [Nat.sub_add_cancel hk1]; omega)
  exact hshort (a (k - 1) + 1) (a (k - 1) + 2) (by omega) (by omega) (by omega) h1 h2

theorem open_of_gap (ha : Enumeration S a) (hS : ∀ i ∈ S, i ≤ r) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ S.card) (hgap : a (k - 1) + 2 ≤ a k) :
    a (k - 1) + 1 ∉ S ∧ 1 ≤ a (k - 1) + 1 ∧ a (k - 1) + 1 < r := by
  have hr : a k ≤ r := hS _ (ha.mem k hk1 hk2)
  refine ⟨ha.not_mem_between (k := k - 1) (by omega) (by omega)
    (by rw [Nat.sub_add_cancel hk1]; omega), by omega, by omega⟩

theorem gap_eq_one_of_no_short_open (ha : Enumeration S a) (hS : ∀ i ∈ S, i ≤ r)
    (hall : ∀ j, 1 ≤ j → j < r → j ∈ S) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ S.card) :
    a k = a (k - 1) + 1 := by
  have hlt : a (k - 1) < a k := ha.strictMonoOn (by omega) hk2
  by_contra hc
  obtain ⟨h1, h2, h3⟩ := open_of_gap ha hS hk1 hk2 (by omega)
  exact h1 (hall _ h2 h3)

theorem exists_unique_plane_piece (ha : Enumeration S a) (hne : S.Nonempty)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    (hshort : ∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → j₂ < r → j₁ ∉ S → j₂ ∉ S → False)
    (htail : 2 ≤ r → r ∉ S → r - 1 ∉ S → False) {j₀ : ℕ} (hj1 : 1 ≤ j₀) (hjr : j₀ < r)
    (hj₀ : j₀ ∉ S) :
    ∃ k₀, 1 ≤ k₀ ∧ k₀ ≤ S.card ∧ a k₀ = a (k₀ - 1) + 2 ∧
      ∀ k, 1 ≤ k → k ≤ S.card → k ≠ k₀ → a k = a (k - 1) + 1 := by
  classical
  have hS' : ∀ i ∈ S, i ≤ r := fun i hi => (hS i hi).2
  have hlast := ha.last_mem hne
  have hslt : j₀ < a S.card := by
    by_cases hrS : r ∈ S
    · have := ha.le_last hrS
      omega
    · have hr1 : r - 1 ∈ S := by
        by_contra hr1
        exact htail (by omega) hrS hr1
      have := ha.le_last hr1
      have hne' : j₀ ≠ r - 1 := fun e => hj₀ (e ▸ hr1)
      omega
  have hex : ∃ k, j₀ < a k := ⟨S.card, hslt⟩
  obtain ⟨k, hkspec, hkmin⟩ : ∃ k, j₀ < a k ∧ ∀ m < k, ¬ j₀ < a m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hkle : k ≤ S.card := by
    by_contra hc
    exact hkmin S.card (by omega) hslt
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    rw [this, ha.zero] at hkspec
    omega
  have hprev : a (k - 1) ≤ j₀ := by
    have := hkmin (k - 1) (by omega)
    omega
  have hprev' : a (k - 1) ≠ j₀ := by
    intro e
    rcases Nat.eq_zero_or_pos (k - 1) with h0 | h0
    · rw [h0, ha.zero] at e
      omega
    · exact hj₀ (e ▸ ha.mem (k - 1) h0 (by omega))
  have hgap2 : a k = a (k - 1) + 2 := by
    have := gap_le_two ha hS' hshort hk1 hkle
    omega
  refine ⟨k, hk1, hkle, hgap2, fun k' hk'1 hk'2 hne2 => ?_⟩
  have hlt : a (k' - 1) < a k' := ha.strictMonoOn (by omega) hk'2
  have hle2 := gap_le_two ha hS' hshort hk'1 hk'2
  by_contra hc
  obtain ⟨h1, h2, h3⟩ := open_of_gap ha hS' hk'1 hk'2 (by omega)
  have hj0eq : a (k - 1) + 1 = j₀ := by omega
  rcases lt_or_gt_of_ne (Ne.symm hne2) with hlt' | hgt'
  · have : a k ≤ a (k' - 1) := by
      rcases (show k ≤ k' - 1 by omega).eq_or_lt with e | e
      · rw [e]
      · exact (ha.strictMonoOn e (show k' - 1 ≤ S.card by omega)).le
    exact hshort j₀ (a (k' - 1) + 1) hj1 (by omega) h3 hj₀ h1
  · have : a k' ≤ a (k - 1) := by
      rcases (show k' ≤ k - 1 by omega).eq_or_lt with e | e
      · rw [e]
      · exact (ha.strictMonoOn e (show k - 1 ≤ S.card by omega)).le
    exact hshort (a (k' - 1) + 1) j₀ h2 (by omega) hjr h1 hj₀

theorem le_last_of_tail (ha : Enumeration S a) (hne : S.Nonempty) (hS : ∀ i ∈ S, i ≤ r)
    (htail : 2 ≤ r → r ∉ S → r - 1 ∉ S → False) (hr : 2 ≤ r) :
    r - 1 ≤ a S.card ∧ a S.card ≤ r := by
  refine ⟨?_, hS _ (ha.last_mem hne)⟩
  by_cases hrS : r ∈ S
  · have := ha.le_last hrS
    omega
  · have hr1 : r - 1 ∈ S := by
      by_contra hr1
      exact htail hr hrS hr1
    have := ha.le_last hr1
    omega

end Gaps

section Survivors

theorem survivors_of_dim_le_seven {r ε : ℕ} {I : Set ℕ} (hε : ε ≤ 1) (hn : 4 ≤ 2 * r + ε)
    (h7 : 2 * r + ε ≤ 7) (hI : I ⊆ Set.Icc 1 r) (hne : I.Nonempty)
    (hshort : ∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → j₂ < r → j₁ ∉ I → j₂ ∉ I → False)
    (htail : 2 ≤ r → r ∉ I → r - 1 ∉ I → False) (hopen : ∃ j, 1 ≤ j ∧ j < r ∧ j ∉ I) :
    (r = 2 ∧ ε = 0 ∧ I = {2}) ∨ (r = 2 ∧ ε = 1 ∧ I = {2}) ∨
    (r = 3 ∧ ε = 0 ∧ I = {2}) ∨ (r = 3 ∧ ε = 0 ∧ I = {1, 3}) ∨ (r = 3 ∧ ε = 0 ∧ I = {2, 3}) ∨
    (r = 3 ∧ ε = 1 ∧ I = {1, 3}) ∨ (r = 3 ∧ ε = 1 ∧ I = {2, 3}) ∨ (r = 3 ∧ ε = 1 ∧ I = {2}) := by
  obtain ⟨j₀, hj1, hjr, hj₀⟩ := hopen
  obtain ⟨x, hx⟩ := hne
  have hr23 : r = 2 ∨ r = 3 := by omega
  rcases hr23 with rfl | rfl
  · have hj : j₀ = 1 := by omega
    subst hj
    have hI2 : I = {2} := by
      ext i
      constructor
      · intro hi
        have := hI hi
        simp only [Set.mem_Icc] at this
        have : i ≠ 1 := fun e => hj₀ (e ▸ hi)
        simp only [Set.mem_singleton_iff]
        omega
      · intro hi
        simp only [Set.mem_singleton_iff] at hi
        subst hi
        have := hI hx
        simp only [Set.mem_Icc] at this
        have : x ≠ 1 := fun e => hj₀ (e ▸ hx)
        have : x = 2 := by omega
        exact this ▸ hx
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · exact Or.inl ⟨rfl, rfl, hI2⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, hI2⟩)
  · have key : ∀ i, i ∈ I ↔ (i = 1 ∧ 1 ∈ I) ∨ (i = 2 ∧ 2 ∈ I) ∨ (i = 3 ∧ 3 ∈ I) := by
      intro i
      constructor
      · intro hi
        have := hI hi
        simp only [Set.mem_Icc] at this
        rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
        · exact Or.inl ⟨rfl, hi⟩
        · exact Or.inr (Or.inl ⟨rfl, hi⟩)
        · exact Or.inr (Or.inr ⟨rfl, hi⟩)
      · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;> exact h
    have hj12 : j₀ = 1 ∨ j₀ = 2 := by omega
    have e13 : ∀ (h1 : 1 ∈ I) (h2 : 2 ∉ I) (h3 : 3 ∈ I), I = {1, 3} := by
      intro h1 h2 h3
      ext i
      rw [key i]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (⟨rfl, _⟩ | ⟨rfl, h⟩ | ⟨rfl, _⟩)
        · exact Or.inl rfl
        · exact absurd h h2
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact Or.inl ⟨rfl, h1⟩
        · exact Or.inr (Or.inr ⟨rfl, h3⟩)
    have e23 : ∀ (h1 : 1 ∉ I) (h2 : 2 ∈ I) (h3 : 3 ∈ I), I = {2, 3} := by
      intro h1 h2 h3
      ext i
      rw [key i]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (⟨rfl, h⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩)
        · exact absurd h h1
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact Or.inr (Or.inl ⟨rfl, h2⟩)
        · exact Or.inr (Or.inr ⟨rfl, h3⟩)
    have e2 : ∀ (h1 : 1 ∉ I) (h2 : 2 ∈ I) (h3 : 3 ∉ I), I = {2} := by
      intro h1 h2 h3
      ext i
      rw [key i]
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro (⟨rfl, h⟩ | ⟨rfl, _⟩ | ⟨rfl, h⟩)
        · exact absurd h h1
        · rfl
        · exact absurd h h3
      · rintro rfl
        exact Or.inr (Or.inl ⟨rfl, h2⟩)
    have hcases : (1 ∈ I ∧ 2 ∉ I ∧ 3 ∈ I) ∨ (1 ∉ I ∧ 2 ∈ I ∧ 3 ∈ I) ∨ (1 ∉ I ∧ 2 ∈ I ∧ 3 ∉ I) := by
      by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I <;> by_cases h3 : 3 ∈ I
      · rcases hj12 with rfl | rfl <;> contradiction
      · rcases hj12 with rfl | rfl <;> contradiction
      · exact Or.inl ⟨h1, h2, h3⟩
      · exact (htail (by omega) h3 h2).elim
      · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
      · exact (hshort 1 2 le_rfl (by omega) (by omega) h1 h2).elim
      · exact (hshort 1 2 le_rfl (by omega) (by omega) h1 h2).elim
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, e13 h1 h2 h3⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, e23 h1 h2 h3⟩))))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, e2 h1 h2 h3⟩))
    · rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, e13 h1 h2 h3⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, e23 h1 h2 h3⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, e2 h1 h2 h3⟩))))))

end Survivors

end CFSG.HardMathSupport.Curtis.UnitaryLevi
