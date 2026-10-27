module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup

@[expose] def fixAut {C : Type*} [Group C] (α : MulAut C) : Subgroup C where
  carrier := {c | α c = c}
  one_mem' := map_one α
  mul_mem' {a b} ha hb := by
    have ha' : α a = a := ha
    have hb' : α b = b := hb
    show α (a * b) = a * b
    rw [map_mul, ha', hb']
  inv_mem' {a} ha := by
    have ha' : α a = a := ha
    show α a⁻¹ = a⁻¹
    rw [map_inv, ha']

theorem mem_fixAut {C : Type*} [Group C] {α : MulAut C} {c : C} : c ∈ fixAut α ↔ α c = c :=
  Iff.rfl

@[expose] noncomputable def fxFun {Y C : Type*} [Group Y] [Group C] (act : Y →* MulAut C)
    (y : Y) : ℕ :=
  Nat.card (fixAut (act y))

variable {Y C : Type*} [Group Y] [Group C] (act : Y →* MulAut C)

theorem mem_fixAut_conj {s y : Y} {c : C} :
    c ∈ fixAut (act (s * y * s⁻¹)) ↔ (act s)⁻¹ c ∈ fixAut (act y) := by
  have hc : act s ((act s)⁻¹ c) = c := by simp
  simp only [mem_fixAut, map_mul, map_inv, MulAut.mul_apply]
  constructor
  · intro h
    exact (act s).injective (h.trans hc.symm)
  · intro h
    rw [h]
    exact hc

theorem fxFun_conj (s y : Y) : fxFun act (s * y * s⁻¹) = fxFun act y := by
  unfold fxFun
  refine Nat.card_congr
    { toFun := fun c => ⟨(act s)⁻¹ c.1, (mem_fixAut_conj act).1 c.2⟩
      invFun := fun c => ⟨act s c.1, (mem_fixAut_conj act).2 (by simp)⟩
      left_inv := fun c => Subtype.ext (by simp)
      right_inv := fun c => Subtype.ext (by simp) }

theorem fixAut_le_pow (y : Y) (k : ℕ) : fixAut (act y) ≤ fixAut (act (y ^ k)) := by
  intro c hc
  have hc' : act y c = c := hc
  show act (y ^ k) c = c
  rw [map_pow]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, hc', ih]

theorem fxFun_le_pow [Finite C] (y : Y) (k : ℕ) : fxFun act y ≤ fxFun act (y ^ k) :=
  Subgroup.card_le_of_le (fixAut_le_pow act y k)

theorem fixAut_inf_le (y y' : Y) : fixAut (act y) ⊓ fixAut (act y') ≤ fixAut (act (y * y')) := by
  intro c hc
  have h1 : act y c = c := (mem_inf.1 hc).1
  have h2 : act y' c = c := (mem_inf.1 hc).2
  show act (y * y') c = c
  rw [map_mul, MulAut.mul_apply, h2, h1]

theorem card_mul_card_le {C : Type*} [Group C] [Finite C] (A B : Subgroup C) :
    Nat.card A * Nat.card B ≤ Nat.card C * Nat.card ↥(A ⊓ B) := by
  have hA := A.card_mul_index
  have hB := B.card_mul_index
  have hD := (A ⊓ B).card_mul_index
  have hidx : (A ⊓ B).index ≤ A.index * B.index := Subgroup.index_inf_le
  have hApos : 0 < A.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hBpos : 0 < B.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.le_of_mul_le_mul_right (c := A.index * B.index) ?_ (Nat.mul_pos hApos hBpos)
  calc Nat.card A * Nat.card B * (A.index * B.index)
      = (Nat.card A * A.index) * (Nat.card B * B.index) := by ring
    _ = Nat.card C * Nat.card C := by rw [hA, hB]
    _ = Nat.card C * (Nat.card ↥(A ⊓ B) * (A ⊓ B).index) := by rw [hD]
    _ ≤ Nat.card C * (Nat.card ↥(A ⊓ B) * (A.index * B.index)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hidx)
    _ = Nat.card C * Nat.card ↥(A ⊓ B) * (A.index * B.index) := by ring

theorem fxFun_mul_le [Finite C] (y y' : Y) :
    fxFun act y * fxFun act y' ≤ Nat.card C * fxFun act (y * y') :=
  (card_mul_card_le (fixAut (act y)) (fixAut (act y'))).trans
    (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (fixAut_inf_le act y y')))

end CFSG.EvenSporadicStandard.M24Std.CU43
