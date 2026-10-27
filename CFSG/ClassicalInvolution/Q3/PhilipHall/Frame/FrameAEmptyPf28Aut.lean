module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf27Q8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out

open QuaternionGroup

def S0 : Finset Q8 := {a 0, a 1, a 2, a 3}

def S1 : Finset Q8 := {a 0, a 2, xa 0, xa 2}

theorem idxFin_S0 : IdxFin S0 := by decide +kernel

theorem idxFin_S1 : IdxFin S1 := by decide +kernel

@[expose] def idx2Of (s : Finset Q8) (hs : IdxFin s) : Idx2 Q8 :=
  ⟨mkSub s hs, by rw [card_mkSub, hs.2.2.2, card_q8]⟩

theorem q8_gen : ∀ y : Q8, ∃ i : Fin 4, ∃ j : Fin 2,
    y = (a 1 : Q8) ^ (i : ℕ) * (xa 0 : Q8) ^ (j : ℕ) := by decide +kernel

theorem q8_pairs : ∀ p q : Q8, p ∈ S0 → q ∈ S1 → p * p ≠ 1 → q * q ≠ 1 →
    ∃ g : Q8, p = g * a 1 * g⁻¹ ∧ q = g * xa 0 * g⁻¹ := by
  unfold S0 S1
  decide +kernel

theorem a2_ne_one : (a 2 : Q8) ≠ 1 := by decide

theorem exists_inner_of_act_eq_one (α : MulAut Q8) (h : Idx2.act α = 1) :
    ∃ g : Q8, ∀ y, α y = g * y * g⁻¹ := by
  have key : ∀ (s : Finset Q8) (hs : IdxFin s) (x : Q8), x ∈ s → α x ∈ s := by
    intro s hs x hx
    have h1 := Idx2.act_apply α (idx2Of s hs) (α x)
    rw [h, MulEquiv.symm_apply_apply] at h1
    exact h1.mpr hx
  have hp : α (a 1) ∈ S0 := key S0 idxFin_S0 _ (by decide)
  have hq : α (xa 0) ∈ S1 := key S1 idxFin_S1 _ (by decide)
  have h2 : α (a 2) ≠ 1 := by
    intro h0
    apply a2_ne_one
    have : α (a 2) = α 1 := by rw [h0, map_one]
    exact α.injective this
  have e1 : (a 1 : Q8) * a 1 = a 2 := by decide
  have e2 : (xa 0 : Q8) * xa 0 = a 2 := by decide
  have hp2 : α (a 1) * α (a 1) ≠ 1 := by rw [← map_mul, e1]; exact h2
  have hq2 : α (xa 0) * α (xa 0) ≠ 1 := by rw [← map_mul, e2]; exact h2
  obtain ⟨g, hg1, hg2⟩ := q8_pairs _ _ hp hq hp2 hq2
  refine ⟨g, fun y => ?_⟩
  obtain ⟨i, j, rfl⟩ := q8_gen y
  rw [map_mul, map_pow, map_pow, hg1, hg2, conj_pow, conj_pow]
  group

theorem exists_inner_of_act_eq_one_of_equiv {A : Type} [Group A] (e : A ≃* Q8) (α : MulAut A)
    (h : Idx2.act α = 1) : ∃ g : A, ∀ y, α y = g * y * g⁻¹ := by
  let β : MulAut Q8 := e.symm.trans (α.trans e)
  have hβ : Idx2.act β = 1 := by
    apply Equiv.ext
    intro H
    apply Subtype.ext
    apply Subgroup.ext
    intro x
    rw [Idx2.act_apply]
    show e (α.symm (e.symm x)) ∈ H.1 ↔ x ∈ H.1
    have h1 : α.symm (e.symm x) ∈ ((Idx2.congr e).symm H).1 ↔
        e.symm x ∈ ((Idx2.congr e).symm H).1 := by
      have := Idx2.act_apply α ((Idx2.congr e).symm H) (e.symm x)
      rw [h] at this
      exact this.symm
    rw [Idx2.congr_symm_mem, Idx2.congr_symm_mem, MulEquiv.apply_symm_apply] at h1
    exact h1
  obtain ⟨g, hg⟩ := exists_inner_of_act_eq_one β hβ
  refine ⟨e.symm g, fun y => ?_⟩
  have h2 : e (α y) = g * e y * g⁻¹ := by
    have := hg (e y)
    simpa [β] using this
  have h3 : α y = e.symm (g * e y * g⁻¹) := by
    rw [← h2, MulEquiv.symm_apply_apply]
  rw [h3, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out
