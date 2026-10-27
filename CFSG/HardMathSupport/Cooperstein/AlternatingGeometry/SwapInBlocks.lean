module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IndexTwoBlockUniqueness

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {Ω : Type*} [DecidableEq Ω] {σ : Perm Ω} {c : Ω → Bool}

theorem false_of_swap_dbl {P : Subgroup (Perm Ω)} (hP : IsPGroup 2 P)
    (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x)
    (hdbl : dblGroup σ c ≤ P) {a b y : Ω} (hb1 : b ≠ a) (hb2 : b ≠ σ a) (hy1 : y ≠ a)
    (hy2 : y ≠ σ a) (hyc : c y = c a) (hyb1 : y ≠ b) (hyb2 : σ y ≠ b)
    (ht : swap a b ∈ P) : False := by
  have hg : swap a (σ a) * swap y (σ y) ∈ P :=
    hdbl (Subgroup.subset_closure ⟨a, y, hy1, hy2, hyc, rfl⟩)
  have hσy : σ y ≠ a := fun h => hy2 (by rw [← h, hσ2])
  have hσy' : σ y ≠ σ a := fun h => hy1 (σ.injective h)
  have hσa : σ a ≠ a := hσ1 a
  have hP' := P.mul_mem ht hg
  refine not_isPGroup_of_threeCycle hP hP' (a := a) (b := σ a) (c := b) hσa.symm hb2.symm hb1 ?_ ?_ ?_
  · simp only [Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hy1.symm hσy.symm, swap_apply_left,
      swap_apply_of_ne_of_ne hσa hb2.symm.symm.symm]
  · simp only [Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hy2.symm hσy'.symm, swap_apply_right, swap_apply_left]
  · simp only [Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hyb1.symm hyb2.symm, swap_apply_of_ne_of_ne hb1 hb2, swap_apply_right]

section Fin

variable [Fintype Ω]

theorem eq_matching_of_swap_mem (hcard : 6 ≤ Fintype.card Ω)
    (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (hc : ∀ x, c (σ x) = c x)
    (h4 : ∀ x, (cls c x).card ≠ 4) {P : Subgroup (Perm Ω)} (hP : IsPGroup 2 P)
    (hdbl : dblGroup σ c ≤ P) {a b : Ω} (hab : a ≠ b) (ht : swap a b ∈ P) : b = σ a := by
  by_contra hb
  have hb1 : b ≠ a := hab.symm
  have ha2 : a ≠ σ b := fun h => hb (by rw [h, hσ2])
  have hσab : σ a ≠ σ b := fun h => hab (σ.injective h)
  have hσa : σ a ≠ a := hσ1 a
  have hσb : σ b ≠ b := hσ1 b
  by_cases hA : ∃ y, c y = c a ∧ y ≠ a ∧ y ≠ σ a ∧ y ≠ b ∧ σ y ≠ b
  · obtain ⟨y, hyc, hy1, hy2, hy3, hy4⟩ := hA
    exact false_of_swap_dbl hP hσ1 hσ2 hdbl hb1 hb hy1 hy2 hyc hy3 hy4 ht
  by_cases hB : ∃ y, c y = c b ∧ y ≠ b ∧ y ≠ σ b ∧ y ≠ a ∧ σ y ≠ a
  · obtain ⟨y, hyc, hy1, hy2, hy3, hy4⟩ := hB
    refine false_of_swap_dbl hP hσ1 hσ2 hdbl (a := b) (b := a) (y := y) hab ha2 hy1 hy2 hyc hy3 hy4 ?_
    rwa [swap_comm]
  push Not at hA hB
  have hmemA : ∀ y, c y = c a → y = a ∨ y = σ a ∨ y = b ∨ y = σ b := by
    intro y hy
    by_cases h1 : y = a
    · exact Or.inl h1
    by_cases h2 : y = σ a
    · exact Or.inr (Or.inl h2)
    by_cases h3 : y = b
    · exact Or.inr (Or.inr (Or.inl h3))
    have h4' : σ y = b := by
      by_contra h; exact absurd (hA y hy h1 h2 h3) h
    right; right; right
    rw [← hσ2 y, h4']
  have hmemB : ∀ y, c y = c b → y = a ∨ y = σ a ∨ y = b ∨ y = σ b := by
    intro y hy
    by_cases h1 : y = b
    · exact Or.inr (Or.inr (Or.inl h1))
    by_cases h2 : y = σ b
    · exact Or.inr (Or.inr (Or.inr h2))
    by_cases h3 : y = a
    · exact Or.inl h3
    have h4' : σ y = a := by
      by_contra h; exact absurd (hB y hy h1 h2 h3) h
    right; left
    rw [← hσ2 y, h4']
  by_cases hcab : c a = c b
  · apply h4 a
    have : cls c a = {a, σ a, b, σ b} := by
      apply Finset.Subset.antisymm
      · intro y hy
        have hy' : c y = c a := (mem_cls_iff c).1 hy
        simpa using hmemA y hy'
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rw [mem_cls_iff]
        rcases hy with rfl | rfl | rfl | rfl
        · rfl
        · exact hc _
        · exact hcab.symm
        · rw [hc]; exact hcab.symm
    rw [this]
    simp [Finset.card_insert_of_notMem, hσa.symm, hab, ha2, hσab, hσa, hσb, hb1, hb,
      Ne.symm hσa, Ne.symm hσb, Ne.symm hb, ha2.symm, hσab.symm, hab.symm]
  ·
    have hΩ : (Finset.univ : Finset Ω) ⊆ {a, σ a, b, σ b} := by
      intro y _
      cases hya : c y
      · cases hcb : c b
        · exact by
            have := hmemB y (by rw [hya, hcb])
            simpa using this
        · cases hca : c a
          · have := hmemA y (by rw [hya, hca])
            simpa using this
          · exact absurd (hca.trans hcb.symm) hcab
      · cases hcb : c b
        · cases hca : c a
          · exact absurd (hca.trans hcb.symm) hcab
          · have := hmemA y (by rw [hya, hca])
            simpa using this
        · have := hmemB y (by rw [hya, hcb])
          simpa using this
    have := Finset.card_le_card hΩ
    rw [Finset.card_univ] at this
    have h4c : ({a, σ a, b, σ b} : Finset Ω).card ≤ 4 := Finset.card_le_four
    omega

end Fin

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
