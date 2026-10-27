module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanBasic
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.QuasithinUnique.ONan

open Module

theorem ncard_pair_le {α : Type*} (a b : α) : ({a, b} : Set α).ncard ≤ 2 := by
  refine (Set.ncard_insert_le a {b}).trans ?_
  rw [Set.ncard_singleton]

variable {A C : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
  [AddCommGroup C] [Finite C]

theorem corr_lower {D F : Set C} {Q : Set (A × C)}
    (hQ : ∀ a e, (a, e) ∈ Q ↔ (a ≠ 0 ∧ e ∈ D) ∨ (a = 0 ∧ e ∈ F)) {b : A} {t : C}
    (ht : ∀ e ∈ D, e + t ∈ D) :
    (Nat.card A - 2) * D.ncard ≤ {p : A × C | p ∈ Q ∧ p + (b, t) ∈ Q}.ncard := by
  have hsub : ({0, b}ᶜ : Set A) ×ˢ D ⊆ {p : A × C | p ∈ Q ∧ p + (b, t) ∈ Q} := by
    rintro ⟨a, e⟩ ⟨ha, he⟩
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ha
    obtain ⟨ha0, hab⟩ := ha
    refine ⟨(hQ a e).mpr (Or.inl ⟨ha0, he⟩), ?_⟩
    show (a + b, e + t) ∈ Q
    rw [hQ]
    exact Or.inl ⟨(add_ne_zero_iff_ne a b).mpr hab, ht e he⟩
  calc (Nat.card A - 2) * D.ncard ≤ ({0, b}ᶜ : Set A).ncard * D.ncard := by
        apply Nat.mul_le_mul_right
        rw [Set.ncard_compl]
        have := ncard_pair_le (0 : A) b
        omega
    _ = (({0, b}ᶜ : Set A) ×ˢ D).ncard := Set.ncard_prod.symm
    _ ≤ _ := Set.ncard_le_ncard hsub

theorem corr_upper_ne {D F : Set C} {Q : Set (A × C)}
    (hQ : ∀ a e, (a, e) ∈ Q ↔ (a ≠ 0 ∧ e ∈ D) ∨ (a = 0 ∧ e ∈ F)) {b : A} (hb : b ≠ 0) {t : C}
    (ht : ∃ e ∈ D, e + t ∉ D) :
    {p : A × C | p ∈ Q ∧ p + (b, t) ∈ Q}.ncard ≤
      (Nat.card A - 2) * (D.ncard - 1) + 2 * D.ncard := by
  let M : Set C := {e | e ∈ D ∧ e + t ∈ D}
  let G : Set C := {e | e ∈ F ∧ e + t ∈ D}
  let H : Set C := {e | e ∈ D ∧ e + t ∈ F}
  have hsub : {p : A × C | p ∈ Q ∧ p + (b, t) ∈ Q} ⊆
      ((({0, b}ᶜ : Set A) ×ˢ M ∪ ({0} : Set A) ×ˢ G) ∪ ({b} : Set A) ×ˢ H) := by
    rintro ⟨a, e⟩ ⟨h1, h2⟩
    have h2' : (a + b, e + t) ∈ Q := h2
    rw [hQ] at h1 h2'
    by_cases ha0 : a = 0
    · subst ha0
      have he : e ∈ F := by
        rcases h1 with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd rfl h
        · exact h
      have het : e + t ∈ D := by
        rcases h2' with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd (by simpa using h) hb
      exact Or.inl (Or.inr ⟨rfl, he, het⟩)
    · have he : e ∈ D := by
        rcases h1 with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h ha0
      by_cases hab : a = b
      · subst hab
        have het : e + t ∈ F := by
          rcases h2' with ⟨h, -⟩ | ⟨-, h⟩
          · exact absurd (ZModModule.add_self a) h
          · exact h
        exact Or.inr ⟨rfl, he, het⟩
      · have het : e + t ∈ D := by
          rcases h2' with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · exact absurd ((add_eq_zero_iff_eq a b).mp h) hab
        refine Or.inl (Or.inl ⟨?_, he, het⟩)
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨ha0, hab⟩
  have hMD : M ⊂ D := by
    refine ⟨fun e he => he.1, fun hDM => ?_⟩
    obtain ⟨e, he, het⟩ := ht
    exact het (hDM he).2
  have hM : M.ncard ≤ D.ncard - 1 := by
    have := Set.ncard_lt_ncard hMD
    omega
  have hG : G.ncard ≤ D.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun e => e + t) (fun e he => he.2) ?_
    intro x _ y _ h
    exact add_right_cancel h
  have hH : H.ncard ≤ D.ncard := Set.ncard_le_ncard (fun e he => he.1)
  have hcompl : ({0, b}ᶜ : Set A).ncard = Nat.card A - 2 := by
    rw [Set.ncard_compl, Set.ncard_pair (Ne.symm hb)]
  calc _ ≤ ((({0, b}ᶜ : Set A) ×ˢ M ∪ ({0} : Set A) ×ˢ G) ∪ ({b} : Set A) ×ˢ H).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (({0, b}ᶜ : Set A) ×ˢ M ∪ ({0} : Set A) ×ˢ G).ncard + (({b} : Set A) ×ˢ H).ncard :=
        Set.ncard_union_le _ _
    _ ≤ (({0, b}ᶜ : Set A) ×ˢ M).ncard + (({0} : Set A) ×ˢ G).ncard +
          (({b} : Set A) ×ˢ H).ncard := by
        have := Set.ncard_union_le (({0, b}ᶜ : Set A) ×ˢ M) (({0} : Set A) ×ˢ G)
        omega
    _ = (Nat.card A - 2) * M.ncard + G.ncard + H.ncard := by
        rw [Set.ncard_prod, Set.ncard_prod, Set.ncard_prod, hcompl, Set.ncard_singleton,
          Set.ncard_singleton, one_mul, one_mul]
    _ ≤ (Nat.card A - 2) * (D.ncard - 1) + 2 * D.ncard := by
        have := Nat.mul_le_mul_left (Nat.card A - 2) hM
        omega

omit [Module (ZMod 2) A] in
theorem corr_upper_zero {D F : Set C} {Q : Set (A × C)}
    (hQ : ∀ a e, (a, e) ∈ Q ↔ (a ≠ 0 ∧ e ∈ D) ∨ (a = 0 ∧ e ∈ F)) (hF : (0 : C) ∉ F) {t : C}
    (ht : ∃ e ∈ D, e + t ∉ D) :
    {p : A × C | p ∈ Q ∧ p + (0, t) ∈ Q}.ncard ≤
      (Nat.card A - 1) * (D.ncard - 1) + (Nat.card C - 1) := by
  let M : Set C := {e | e ∈ D ∧ e + t ∈ D}
  have hsub : {p : A × C | p ∈ Q ∧ p + (0, t) ∈ Q} ⊆
      (({0}ᶜ : Set A) ×ˢ M ∪ ({0} : Set A) ×ˢ F) := by
    rintro ⟨a, e⟩ ⟨h1, h2⟩
    have h2' : (a + 0, e + t) ∈ Q := h2
    rw [hQ] at h1 h2'
    by_cases ha0 : a = 0
    · subst ha0
      have he : e ∈ F := by
        rcases h1 with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd rfl h
        · exact h
      exact Or.inr ⟨rfl, he⟩
    · have he : e ∈ D := by
        rcases h1 with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h ha0
      have het : e + t ∈ D := by
        rcases h2' with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · rw [add_zero] at h
          exact absurd h ha0
      exact Or.inl ⟨ha0, he, het⟩
  have hMD : M ⊂ D := by
    refine ⟨fun e he => he.1, fun hDM => ?_⟩
    obtain ⟨e, he, het⟩ := ht
    exact het (hDM he).2
  have hM : M.ncard ≤ D.ncard - 1 := by
    have := Set.ncard_lt_ncard hMD
    omega
  have hFle : F.ncard ≤ Nat.card C - 1 := by
    have h1 : F ⊆ ({0}ᶜ : Set C) := fun e he h => hF (h ▸ he)
    have h2 := Set.ncard_le_ncard h1
    rw [Set.ncard_compl, Set.ncard_singleton] at h2
    exact h2
  calc _ ≤ ((({0}ᶜ : Set A) ×ˢ M) ∪ ({0} : Set A) ×ˢ F).ncard := Set.ncard_le_ncard hsub
    _ ≤ (({0}ᶜ : Set A) ×ˢ M).ncard + (({0} : Set A) ×ˢ F).ncard := Set.ncard_union_le _ _
    _ = (Nat.card A - 1) * M.ncard + F.ncard := by
        rw [Set.ncard_prod, Set.ncard_prod, Set.ncard_compl, Set.ncard_singleton, one_mul]
    _ ≤ (Nat.card A - 1) * (D.ncard - 1) + (Nat.card C - 1) := by
        have := Nat.mul_le_mul_left (Nat.card A - 1) hM
        omega

theorem corr_dichotomy {D F : Set C} {Q : Set (A × C)}
    (hQ : ∀ a e, (a, e) ∈ Q ↔ (a ≠ 0 ∧ e ∈ D) ∨ (a = 0 ∧ e ∈ F)) (hF : (0 : C) ∉ F)
    (hk : 1 ≤ D.ncard) (hks : 2 * D.ncard ≤ Nat.card C) (hs : 4 ≤ Nat.card C)
    (hq : 2 * Nat.card C ≤ Nat.card A) (b : A) (t : C) :
    ((∀ e ∈ D, e + t ∈ D) →
      (Nat.card A - 2) * D.ncard ≤ {p : A × C | p ∈ Q ∧ p + (b, t) ∈ Q}.ncard) ∧
    ((∃ e ∈ D, e + t ∉ D) →
      {p : A × C | p ∈ Q ∧ p + (b, t) ∈ Q}.ncard < (Nat.card A - 2) * D.ncard) := by
  refine ⟨fun ht => corr_lower hQ ht, fun ht => ?_⟩
  obtain ⟨k₁, hk₁⟩ : ∃ k₁, D.ncard = k₁ + 1 := ⟨D.ncard - 1, by omega⟩
  obtain ⟨q₁, hq₁⟩ : ∃ q₁, Nat.card A = q₁ + 2 := ⟨Nat.card A - 2, by omega⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, Nat.card C = s₁ + 1 := ⟨Nat.card C - 1, by omega⟩
  by_cases hb : b = 0
  · subst hb
    refine lt_of_le_of_lt (corr_upper_zero hQ hF ht) ?_
    rw [hk₁, hq₁, hs₁]
    rw [hk₁] at hks
    rw [hs₁] at hks hs
    rw [hs₁, hq₁] at hq
    have h1 : q₁ + 2 - 1 = q₁ + 1 := by omega
    simp only [Nat.add_sub_cancel, h1]
    nlinarith
  · refine lt_of_le_of_lt (corr_upper_ne hQ hb ht) ?_
    rw [hk₁, hq₁]
    rw [hk₁] at hks
    rw [hs₁] at hks hs
    rw [hs₁, hq₁] at hq
    simp only [Nat.add_sub_cancel]
    nlinarith

end CFSG.QuasithinUnique.ONan
