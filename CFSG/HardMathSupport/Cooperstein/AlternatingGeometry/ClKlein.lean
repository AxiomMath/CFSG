module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOrbits

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender (IsExp2)

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem klein_fix_free {E : Subgroup (Perm Ω)} (hE : IsExp2 E) {e : Fin 4 → Ω}
    (he : Function.Injective e) (horb : ∀ z, z ∈ orbit E (e 0) ↔ z ∈ Set.range e) {ε : Perm Ω}
    (hε : ε ∈ E) {j : Fin 4} (hj : j ≠ 0) (hεj : ε (e 0) = e j) {i : Fin 4} :
    ε (e i) ≠ e i := by
  intro hfix
  obtain ⟨⟨h, hh⟩, hhi⟩ := (horb (e i)).2 ⟨i, rfl⟩
  have hcomm : ε * h = h * ε := hE.comm hε hh
  have h1 : ε (h (e 0)) = h (ε (e 0)) := by
    have := congrArg (fun f : Perm Ω => f (e 0)) hcomm
    simpa [Perm.mul_apply] using this
  have hhi' : h (e 0) = e i := hhi
  rw [hhi', hfix, hεj] at h1
  have : e 0 = e j := h.injective (hhi'.trans h1)
  exact hj (he this).symm

theorem klein_involution {E : Subgroup (Perm Ω)} (hE : IsExp2 E) {ε : Perm Ω} (hε : ε ∈ E)
    (x : Ω) : ε (ε x) = x := by
  have := hE ε hε
  have h2 := congrArg (fun f : Perm Ω => f x) this
  simpa [Perm.mul_apply] using h2

theorem klein_other {E : Subgroup (Perm Ω)} (hE : IsExp2 E) {e : Fin 4 → Ω}
    (he : Function.Injective e) (horb : ∀ z, z ∈ orbit E (e 0) ↔ z ∈ Set.range e) {ε : Perm Ω}
    (hε : ε ∈ E) {j : Fin 4} (hj : j ≠ 0) (hεj : ε (e 0) = e j) {k l : Fin 4} (hk : k ≠ 0)
    (hkj : k ≠ j) (hl : l ≠ 0) (hlj : l ≠ j) (hkl : k ≠ l) : ε (e k) = e l := by
  have hpres : ∀ i, ∃ k, ε (e i) = e k := by
    intro i
    have : ε (e i) ∈ orbit E (e 0) := by
      obtain ⟨⟨h, hh⟩, hhi⟩ := (horb (e i)).2 ⟨i, rfl⟩
      have h1 : ε (e i) = (ε * h) (e 0) := by rw [Perm.mul_apply]; exact congrArg ε hhi.symm
      exact ⟨⟨ε * h, E.mul_mem hε hh⟩, h1.symm⟩
    obtain ⟨k, hk'⟩ := (horb _).1 this
    exact ⟨k, hk'.symm⟩
  obtain ⟨k', hk'⟩ := hpres k
  have hεj' : ε (e j) = e 0 := by rw [← hεj]; exact klein_involution hE hε _
  have h1 : k' ≠ 0 := by
    intro h; rw [h] at hk'
    exact hkj (he (ε.injective (hk'.trans hεj'.symm)))
  have h2 : k' ≠ j := by
    intro h; rw [h] at hk'
    exact hk (he (ε.injective (hk'.trans hεj.symm)))
  have h3 : k' ≠ k := by
    intro h; rw [h] at hk'
    exact klein_fix_free hE he horb hε hj hεj hk'
  have : k' = l := by
    apply Fin.ext
    have := Fin.val_ne_of_ne h1
    have := Fin.val_ne_of_ne h2
    have := Fin.val_ne_of_ne h3
    have := Fin.val_ne_of_ne hk
    have := Fin.val_ne_of_ne hkj
    have := Fin.val_ne_of_ne hl
    have := Fin.val_ne_of_ne hlj
    have := Fin.val_ne_of_ne hkl
    have := k'.isLt
    have := l.isLt
    have := k.isLt
    have := j.isLt
    simp only [Fin.val_zero] at *
    omega
  rw [hk', this]

theorem klein_elements {E : Subgroup (Perm Ω)} (hE : IsExp2 E) {e : Fin 4 → Ω}
    (he : Function.Injective e) (horb : ∀ z, z ∈ orbit E (e 0) ↔ z ∈ Set.range e) :
    (∃ ε ∈ E, ∀ i, ε (e i) = e ((swap 0 1 * swap 2 3 : Perm (Fin 4)) i)) ∧
    (∃ ε ∈ E, ∀ i, ε (e i) = e ((swap 0 2 * swap 1 3 : Perm (Fin 4)) i)) ∧
    (∃ ε ∈ E, ∀ i, ε (e i) = e ((swap 0 3 * swap 1 2 : Perm (Fin 4)) i)) := by
  have hex : ∀ j : Fin 4, ∃ ε ∈ E, ε (e 0) = e j := by
    intro j
    obtain ⟨⟨ε, hε⟩, hεj⟩ := (horb (e j)).2 ⟨j, rfl⟩
    exact ⟨ε, hε, hεj⟩
  have inv : ∀ {ε : Perm Ω}, ε ∈ E → ∀ x, ε (ε x) = x := fun hε x => klein_involution hE hε x
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ε, hε, h0⟩ := hex 1
    refine ⟨ε, hε, fun i => ?_⟩
    fin_cases i
    · exact h0.trans (congrArg e (by decide))
    · have : ε (e 1) = e 0 := by rw [← h0]; exact inv hε _
      exact this.trans (congrArg e (by decide))
    · have := klein_other hE he horb hε (j := 1) (by decide) h0 (k := 2) (l := 3) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact this.trans (congrArg e (by decide))
    · have := klein_other hE he horb hε (j := 1) (by decide) h0 (k := 3) (l := 2) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact this.trans (congrArg e (by decide))
  · obtain ⟨ε, hε, h0⟩ := hex 2
    refine ⟨ε, hε, fun i => ?_⟩
    fin_cases i
    · exact h0.trans (congrArg e (by decide))
    · have := klein_other hE he horb hε (j := 2) (by decide) h0 (k := 1) (l := 3) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact this.trans (congrArg e (by decide))
    · have : ε (e 2) = e 0 := by rw [← h0]; exact inv hε _
      exact this.trans (congrArg e (by decide))
    · have := klein_other hE he horb hε (j := 2) (by decide) h0 (k := 3) (l := 1) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact this.trans (congrArg e (by decide))
  · obtain ⟨ε, hε, h0⟩ := hex 3
    refine ⟨ε, hε, fun i => ?_⟩
    fin_cases i
    · exact h0.trans (congrArg e (by decide))
    · have := klein_other hE he horb hε (j := 3) (by decide) h0 (k := 1) (l := 2) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact this.trans (congrArg e (by decide))
    · have := klein_other hE he horb hε (j := 3) (by decide) h0 (k := 2) (l := 1) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact this.trans (congrArg e (by decide))
    · have : ε (e 3) = e 0 := by rw [← h0]; exact inv hε _
      exact this.trans (congrArg e (by decide))

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
