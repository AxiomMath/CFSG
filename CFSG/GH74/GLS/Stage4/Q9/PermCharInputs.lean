module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Blocks.InnerProduct
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public meta import Mathlib
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG.TwoRankLowerBound.Helpers
@[expose] def inBL (l : Lg) : Prop :=
  (l.right = 1 ∧ (l.left : Matrix (Fin 2) (Fin 2) F9) 1 0 = 0) ∨
  (l.right ≠ 1 ∧ (l.left : Matrix (Fin 2) (Fin 2) F9) 1 1 = 0)

instance : DecidablePred inBL := fun l => by unfold inBL; infer_instance

namespace PermChar

theorem right_cases (ε : Multiplicative (ZMod 2)) : ε = 1 ∨ ε = Multiplicative.ofAdd 1 := by
  revert ε; decide

theorem ofAdd_one_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

theorem ofAdd_one_mul_self : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by
  decide

theorem sigmaHom_one_apply (M : SL2) : sigmaHom 1 M = M := by
  rw [map_one]; rfl

theorem sigmaHom_ofAdd_one_apply (M : SL2) :
    sigmaHom (Multiplicative.ofAdd 1) M = sigmaAut M := by
  rw [sigmaHom_ofAdd_one]

theorem mul_left_entry (x y : Lg) (i j : Fin 2) :
    ((x * y).left : Matrix (Fin 2) (Fin 2) F9) i j =
      (x.left : Matrix (Fin 2) (Fin 2) F9) i 0 *
          ((sigmaHom x.right y.left : SL2) : Matrix (Fin 2) (Fin 2) F9) 0 j +
        (x.left : Matrix (Fin 2) (Fin 2) F9) i 1 *
          ((sigmaHom x.right y.left : SL2) : Matrix (Fin 2) (Fin 2) F9) 1 j := by
  rw [SemidirectProduct.mul_left, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem inBL_mul {x y : Lg} (hx : inBL x) (hy : inBL y) : inBL (x * y) := by
  rcases x with ⟨M, ε⟩
  rcases y with ⟨N, ε'⟩
  rcases right_cases ε with rfl | rfl <;> rcases right_cases ε' with rfl | rfl <;>
  simp only [inBL, mul_left_entry, SemidirectProduct.mul_right, sigmaHom_one_apply,
    sigmaHom_ofAdd_one_apply, sigmaAut_apply_entries, ofAdd_one_ne_one, ofAdd_one_mul_self,
    mul_one, one_mul, ne_eq, not_true_eq_false, false_and, or_false, false_or,
    not_false_eq_true, true_and] at hx hy ⊢ <;>
  simp [hx, hy]

theorem inv_mk_one (M : SL2) : (⟨M, 1⟩ : Lg)⁻¹ = ⟨M⁻¹, 1⟩ := by
  simp

theorem inv_mk_ofAdd (M : SL2) :
    (⟨M, Multiplicative.ofAdd 1⟩ : Lg)⁻¹ = ⟨sigmaAut M⁻¹, Multiplicative.ofAdd 1⟩ := by
  symm
  apply eq_inv_of_mul_eq_one_left
  apply SemidirectProduct.ext
  · rw [SemidirectProduct.mul_left]
    dsimp only
    rw [sigmaHom_ofAdd_one_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  · rw [SemidirectProduct.mul_right]
    exact ofAdd_one_mul_self

theorem inBL_inv {x : Lg} (hx : inBL x) : inBL x⁻¹ := by
  rcases x with ⟨M, ε⟩
  rcases right_cases ε with rfl | rfl
  · rw [inv_mk_one]
    simp only [inBL, ne_eq, not_true_eq_false, false_and, or_false, true_and] at hx ⊢
    simp [Matrix.adjugate_fin_two, hx]
  · rw [inv_mk_ofAdd]
    simp only [inBL, ofAdd_one_ne_one, ne_eq, not_false_eq_true, false_and, false_or,
      true_and] at hx ⊢
    simp [Matrix.adjugate_fin_two, hx, sigmaAut_apply_entries]

end PermChar

@[expose] def BL : Subgroup Lg where
  carrier := {l | inBL l}
  mul_mem' := PermChar.inBL_mul
  one_mem' := Or.inl ⟨rfl, by simp⟩
  inv_mem' := PermChar.inBL_inv

theorem mem_BL_iff {l : Lg} : l ∈ BL ↔ inBL l := Iff.rfl

instance : DecidablePred (· ∈ BL) := fun _ => decidable_of_iff _ mem_BL_iff.symm

@[expose] def repPt : Option F9 → Lg
  | none => 1
  | some t => ⟨⟨!![t, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩, 1⟩

@[expose] def aTabFast (l : Lg) : ℤ :=
  ((Finset.univ.filter fun p : Option F9 => (repPt p)⁻¹ * l * repPt p ∈ BL).card : ℤ) - 1

@[expose] def aByOrder (inner : Bool) (n : ℕ) : ℤ :=
  if inner then
    (if n = 1 ∨ n = 2 then 9 else if n = 3 ∨ n = 6 then 0 else if n = 4 ∨ n = 8 then 1 else -1)
  else (if n = 16 then 1 else -1)

end CFSG.GH74.GLS.Stage4.Q9
