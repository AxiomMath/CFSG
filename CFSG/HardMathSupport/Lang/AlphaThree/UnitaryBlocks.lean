module

public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.HardMathSupport.Lang.AlphaThree

variable {n : ℕ}

@[expose] def lo (hn : 9 ≤ n) (l : Fin 4) : Fin n := Fin.castLE (by omega) l

@[expose] def hi (hn : 9 ≤ n) (l : Fin 4) : Fin n := Fin.rev (lo hn l)

@[expose] def Bset (hn : 9 ≤ n) (l : Fin 4) : Set (Fin n) := {lo hn l, hi hn l}

theorem val_lo (hn : 9 ≤ n) (l : Fin 4) : (lo hn l).val = l.val := rfl

theorem val_hi (hn : 9 ≤ n) (l : Fin 4) : (hi hn l).val = n - (l.val + 1) := by
  simp [hi, lo, Fin.val_rev]

theorem lo_ne_hi (hn : 9 ≤ n) (l l' : Fin 4) : lo hn l ≠ hi hn l' := by
  intro h
  have h1 := congrArg Fin.val h
  rw [val_lo, val_hi] at h1
  have := l.2
  have := l'.2
  omega

theorem lo_injective (hn : 9 ≤ n) : Function.Injective (lo hn) := by
  intro l l' h
  exact Fin.ext (by simpa [val_lo] using congrArg Fin.val h)

theorem hi_injective (hn : 9 ≤ n) : Function.Injective (hi hn) := by
  intro l l' h
  exact lo_injective hn (Fin.rev_injective h)

theorem rev_hi (hn : 9 ≤ n) (l : Fin 4) : Fin.rev (hi hn l) = lo hn l := by
  simp [hi]

theorem lo_ne_rev_lo (hn : 9 ≤ n) (l : Fin 4) : lo hn l ≠ Fin.rev (lo hn l) :=
  lo_ne_hi hn l l

theorem hi_ne_rev_hi (hn : 9 ≤ n) (l : Fin 4) : hi hn l ≠ Fin.rev (hi hn l) := by
  rw [rev_hi]
  exact (lo_ne_hi hn l l).symm

theorem hi_ne_lo (hn : 9 ≤ n) (l : Fin 4) : hi hn l ≠ lo hn l := (lo_ne_hi hn l l).symm

theorem disjoint_Bset (hn : 9 ≤ n) {l l' : Fin 4} (h : l ≠ l') :
    Disjoint (Bset hn l) (Bset hn l') := by
  rw [Set.disjoint_left]
  rintro a (rfl | rfl) (h' | h')
  · exact h (lo_injective hn h')
  · exact lo_ne_hi hn _ _ h'
  · exact lo_ne_hi hn _ _ h'.symm
  · exact h (hi_injective hn h')

theorem rev_mem_Bset (hn : 9 ≤ n) {a : Fin n} {l : Fin 4} :
    Fin.rev a ∈ Bset hn l ↔ a ∈ Bset hn l := by
  simp only [Bset, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr (Fin.rev_eq_iff.1 h)
    · exact Or.inl ((Fin.rev_eq_iff.1 h).trans (rev_hi hn l))
  · rintro (h | h)
    · exact Or.inr (by rw [h]; rfl)
    · exact Or.inl (by rw [h, rev_hi])

theorem mem_Bset_unique (hn : 9 ≤ n) {a : Fin n} {l l' : Fin 4} (h : a ∈ Bset hn l)
    (h' : a ∈ Bset hn l') : l = l' := by
  by_contra hne
  exact Set.disjoint_left.1 (disjoint_Bset hn hne) h h'

theorem exists_two_good (hn : 9 ≤ n) (a b : Fin n) :
    ∃ l₁ l₂ : Fin 4, l₁ ≠ l₂ ∧ (a ∉ Bset hn l₁ ∧ b ∉ Bset hn l₁) ∧
      (a ∉ Bset hn l₂ ∧ b ∉ Bset hn l₂) := by
  classical
  set bad : Finset (Fin 4) := Finset.univ.filter fun l => a ∈ Bset hn l ∨ b ∈ Bset hn l with hbad
  have h1 : (Finset.univ.filter fun l : Fin 4 => a ∈ Bset hn l).card ≤ 1 :=
    Finset.card_le_one.2 fun l hl l' hl' =>
      mem_Bset_unique hn (Finset.mem_filter.1 hl).2 (Finset.mem_filter.1 hl').2
  have h2 : (Finset.univ.filter fun l : Fin 4 => b ∈ Bset hn l).card ≤ 1 :=
    Finset.card_le_one.2 fun l hl l' hl' =>
      mem_Bset_unique hn (Finset.mem_filter.1 hl).2 (Finset.mem_filter.1 hl').2
  have hbadle : bad.card ≤ 2 := by
    have : bad ⊆ (Finset.univ.filter fun l : Fin 4 => a ∈ Bset hn l) ∪
        (Finset.univ.filter fun l : Fin 4 => b ∈ Bset hn l) := by
      intro l hl
      rcases (Finset.mem_filter.1 hl).2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    exact (Finset.card_le_card this).trans ((Finset.card_union_le _ _).trans (by omega))
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 4)))
    (fun l => a ∈ Bset hn l ∨ b ∈ Bset hn l)
  have hgood : 1 < (Finset.univ.filter fun l : Fin 4 => ¬(a ∈ Bset hn l ∨ b ∈ Bset hn l)).card := by
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    have hb : (Finset.univ.filter fun l : Fin 4 => a ∈ Bset hn l ∨ b ∈ Bset hn l).card ≤ 2 :=
      hbadle
    omega
  obtain ⟨l₁, hl₁, l₂, hl₂, hne⟩ := Finset.one_lt_card.1 hgood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hl₁ hl₂
  exact ⟨l₁, l₂, hne, hl₁, hl₂⟩

end CFSG.HardMathSupport.Lang.AlphaThree
