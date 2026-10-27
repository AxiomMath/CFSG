module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6ThreeCore
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1bGL2

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

section Out

variable {Y : Type} [Group Y]

@[expose] def IsInner (α : MulAut Y) : Prop := ∃ k : Y, ∀ y, α y = k * y * k⁻¹

theorem IsInner.one : IsInner (1 : MulAut Y) := ⟨1, fun y => by simp⟩

theorem IsInner.mul {α β : MulAut Y} (hα : IsInner α) (hβ : IsInner β) : IsInner (α * β) := by
  obtain ⟨k, hk⟩ := hα
  obtain ⟨l, hl⟩ := hβ
  refine ⟨k * l, fun y => ?_⟩
  show α (β y) = k * l * y * (k * l)⁻¹
  rw [hl, hk]
  group

theorem IsInner.pow {α : MulAut Y} (hα : IsInner α) (n : ℕ) : IsInner (α ^ n) := by
  induction n with
  | zero => simpa using IsInner.one
  | succ n ih => rw [pow_succ]; exact ih.mul hα

@[expose] def autFix (α : MulAut Y) : Subgroup Y where
  carrier := {k | α k = k}
  mul_mem' := fun {a b} ha hb => by
    show α (a * b) = a * b
    rw [map_mul]
    have ha' : α a = a := ha
    have hb' : α b = b := hb
    rw [ha', hb']
  one_mem' := by
    show α 1 = 1
    exact map_one α
  inv_mem' := fun {a} ha => by
    show α a⁻¹ = a⁻¹
    rw [map_inv]
    have ha' : α a = a := ha
    rw [ha']

theorem mem_autFix {α : MulAut Y} {k : Y} : k ∈ autFix α ↔ α k = k := Iff.rfl

end Out

structure L27Aut (Y : Type) [Group Y] [Finite Y] : Prop where
  out_mul : ∀ α β : MulAut Y, ¬ IsInner α → ¬ IsInner β → IsInner (α * β)
  outer_fix_card : ∀ α : MulAut Y, ¬ IsInner α → α * α = 1 → Nat.card ↥(autFix α) = 6
  exists_outer_inv : ∀ P : Subgroup Y, Nat.card P = 8 →
    ∃ α : MulAut Y, ¬ IsInner α ∧ α * α = 1 ∧ ∀ y ∈ P, α y ∈ P

theorem L27Aut.isInner_of_odd {Y : Type} [Group Y] [Finite Y] (h : L27Aut Y) {α : MulAut Y}
    (hα : Odd (orderOf α)) : IsInner α := by
  by_contra hne
  have h2 : IsInner (α * α) := h.out_mul α α hne hne
  have hpow : α ^ orderOf α = 1 := pow_orderOf_eq_one α
  obtain ⟨m, hm⟩ := hα
  have e : α = (α * α) ^ (m + 1) := by
    have : α ^ (2 * m + 1) = 1 := by rw [← hm]; exact hpow
    calc α = α * α ^ (2 * m + 1) := by rw [this, mul_one]
      _ = (α * α) ^ (m + 1) := by
        rw [← pow_succ', show (2 * m + 1 + 1) = 2 * (m + 1) by ring, pow_mul, sq]
  exact hne (e ▸ h2.pow (m + 1))

end CFSG.QuasithinUnique.DoubleA3
