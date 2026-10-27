module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OffenderLift

import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

variable {K : Type*} [Group K] {L : Subgroup K} {b c l m : K}

theorem ConjAgree.one : ConjAgree L (1 : K) 1 := fun _ _ => rfl

theorem ConjAgree.inv (hl : l ∈ L) (h : ConjAgree L b l) : ConjAgree L b⁻¹ l⁻¹ := by
  intro k hk
  have h1 : b * (l⁻¹ * k * l) * b⁻¹ = k := by
    have := h (l⁻¹ * k * l) (L.mul_mem (L.mul_mem (L.inv_mem hl) hk) hl)
    rw [this]
    group
  calc b⁻¹ * k * b⁻¹⁻¹ = b⁻¹ * (b * (l⁻¹ * k * l) * b⁻¹) * b⁻¹⁻¹ := by rw [h1]
    _ = l⁻¹ * k * l⁻¹⁻¹ := by group

@[expose] def innerPart (L B : Subgroup K) : Subgroup K where
  carrier := {b | b ∈ B ∧ ∃ l ∈ L, ConjAgree L b l}
  mul_mem' := by
    rintro b c ⟨hb, l, hl, h⟩ ⟨hc, m, hm, h'⟩
    exact ⟨B.mul_mem hb hc, l * m, L.mul_mem hl hm, ConjAgree.mul hl hm h h'⟩
  one_mem' := ⟨B.one_mem, 1, L.one_mem, ConjAgree.one⟩
  inv_mem' := by
    rintro b ⟨hb, l, hl, h⟩
    exact ⟨B.inv_mem hb, l⁻¹, L.inv_mem hl, ConjAgree.inv hl h⟩

theorem mem_innerPart {B : Subgroup K} :
    b ∈ innerPart L B ↔ b ∈ B ∧ ∃ l ∈ L, ConjAgree L b l :=
  Iff.rfl

theorem innerPart_le (L B : Subgroup K) : innerPart L B ≤ B := fun _ h => h.1

end CFSG.LocalAnalysis.RankThreeUC.S15
