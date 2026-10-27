module

public import CFSG.CGT.Timmesfeld75.Sec62Pts

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G]

@[expose] def IsConjPt (T Y A : Subgroup G) : Prop := ∃ a ∈ Y, A = conjSubgroup a T

variable {T T₁ Y : Subgroup G} {n m : ℕ}

theorem IsConjPt.self : IsConjPt T Y T :=
  ⟨1, Y.one_mem, (conjSubgroup_one T).symm⟩

theorem IsConjPt.le {A : Subgroup G} (hT : T ≤ Y) (hA : IsConjPt T Y A) : A ≤ Y := by
  obtain ⟨a, ha, rfl⟩ := hA
  exact conjSubgroup_le_of_le_of_mem hT ha

theorem IsConjPt.card_eq {A : Subgroup G} (hA : IsConjPt T Y A) : Nat.card ↥A = Nat.card ↥T := by
  obtain ⟨a, -, rfl⟩ := hA
  exact card_conjSubgroup a T

theorem IsConjPt.conj {A : Subgroup G} (hA : IsConjPt T Y A) {s : G} (hs : s ∈ Y) :
    IsConjPt T Y (conjSubgroup s A) := by
  obtain ⟨a, ha, rfl⟩ := hA
  exact ⟨s * a, Y.mul_mem hs ha, conjSubgroup_conjSubgroup s a T⟩

theorem IsConjPt.exists_pair {A B : Subgroup G} (hA : IsConjPt T Y A) (hB : IsConjPt T Y B)
    (hne : A ≠ B) : ∃ a ∈ Y, ∃ y ∈ Y, A = conjSubgroup a T ∧
      B = conjSubgroup a (conjSubgroup y T) ∧ conjSubgroup y T ≠ T := by
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨b, hb, rfl⟩ := hB
  refine ⟨a, ha, a⁻¹ * b, Y.mul_mem (Y.inv_mem ha) hb, rfl, ?_, fun h => hne ?_⟩
  · rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  · have := congrArg (conjSubgroup a) h
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left] at this
    exact this.symm

section Pair

variable [Finite G]

omit [Finite G] in
theorem Sec62Ctx.inf_cfgM_conj (P : Sec62Ctx T T₁ Y n m) {a : G} (ha : a ∈ Y) :
    conjSubgroup a T ⊓ cfgM T T₁ = conjSubgroup a (normIn T T₁) := by
  conv_lhs => rw [← P.conj_cfgM ha]
  rw [← conjSubgroup_inf, P.ctx.sec3.cfg.inf_cfgM]

omit [Finite G] in
theorem Sec62Ctx.card_inf_cfgM (P : Sec62Ctx T T₁ Y n m) {A : Subgroup G}
    (hA : IsConjPt T Y A) : Nat.card ↥(A ⊓ cfgM T T₁) = Nat.card ↥(normIn T T₁) := by
  obtain ⟨a, ha, rfl⟩ := hA
  rw [P.inf_cfgM_conj ha, card_conjSubgroup]


theorem Sec62Ctx.inf_eq_bot (P : Sec62Ctx T T₁ Y n m) {A B : Subgroup G} (hA : IsConjPt T Y A)
    (hB : IsConjPt T Y B) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  obtain ⟨a, ha, y, hy, rfl, rfl, hyne⟩ := hA.exists_pair hB hne
  rw [← conjSubgroup_inf, (P.sec3_conj hy hyne).cfg.inf]
  exact conjSubgroup_eq_bot_iff.2 rfl

theorem Sec62Ctx.normIn_eq (P : Sec62Ctx T T₁ Y n m) {A B : Subgroup G} (hA : IsConjPt T Y A)
    (hB : IsConjPt T Y B) (hne : A ≠ B) : normIn A B = A ⊓ cfgM T T₁ := by
  obtain ⟨a, ha, y, hy, rfl, rfl, hyne⟩ := hA.exists_pair hB hne
  rw [normIn_conj, P.normIn_conj_eq hy hyne, P.inf_cfgM_conj ha]

theorem Sec62Ctx.card_sup_eq (P : Sec62Ctx T T₁ Y n m) {A B : Subgroup G} (hA : IsConjPt T Y A)
    (hB : IsConjPt T Y B) (hne : A ≠ B) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥(cfgM T T₁) * (2 ^ m * ((2 ^ m) ^ 2 - 1)) := by
  obtain ⟨a, ha, y, hy, rfl, rfl, hyne⟩ := hA.exists_pair hB hne
  rw [← conjSubgroup_sup_eq_sup, card_conjSubgroup, P.card_sup_conj hy hyne]

end Pair

end CFSG.CGT.Timmesfeld75
