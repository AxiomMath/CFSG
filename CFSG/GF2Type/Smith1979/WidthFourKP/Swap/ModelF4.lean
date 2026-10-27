module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GF2Type.Smith1979.W4Swap.Model

open CFSG.Fischer Matrix
open scoped MatrixGroups

abbrev F4Mat := Matrix (Fin 2) (Fin 2) F4

@[expose] def frob : F4 →+* F4 where
  toFun x := x ^ 2
  map_zero' := by decide
  map_one' := by decide
  map_add' := by decide
  map_mul' := by decide

@[simp] theorem frob_apply (x : F4) : frob x = x ^ 2 := rfl

@[expose] def Act (g X : F4Mat) : F4Mat := g * X * (g.map frob)ᵀ

@[expose] def ActG (g : SL(2, F4)) (X : F4Mat) : F4Mat := Act g.1 X

@[expose] def J : F4Mat := !![0, 1; 1, 0]

abbrev isSL (g : F4Mat) : Prop := g.det = 1

abbrev stabJ (g : F4Mat) : Prop := isSL g ∧ Act g J = J

@[expose] def inv2 (g : F4Mat) : F4Mat := !![g 1 1, g 0 1; g 1 0, g 0 0]

theorem Act_mul (g h : F4Mat) (X : F4Mat) : Act (g * h) X = Act g (Act h X) := by
  simp [Act, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem Act_one (X : F4Mat) : Act 1 X = X := by
  simp [Act, frob]

theorem ActG_mul (g h : SL(2, F4)) (X : F4Mat) :
    ActG (g * h) X = ActG g (ActG h X) := by
  simp [ActG, Act_mul]

theorem ActG_one (X : F4Mat) : ActG 1 X = X := by
  simp [ActG, Act_one]

theorem coe_inv_eq_inv2 (g : SL(2, F4)) : (g⁻¹ : SL(2, F4)).1 = inv2 g.1 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [inv2, CharTwo.neg_eq]

set_option maxRecDepth 10000 in
theorem exists_isSL_act_J_eq (X : F4Mat) (hX : (X.map frob)ᵀ = X) (hd : X.det = 1) :
    ∃ g : F4Mat, isSL g ∧ Act g J = X := by
  revert X
  decide

set_option maxRecDepth 10000 in
theorem card_stabJ : Nat.card {g : F4Mat // stabJ g} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 10000 in
theorem eq_zero_or_eq_J_of_forall_stabJ (Y : F4Mat) (hY : (Y.map frob)ᵀ = Y)
    (hfix : ∀ g : F4Mat, stabJ g → Act g Y = Y) : Y = 0 ∨ Y = J := by
  revert Y
  decide

set_option maxRecDepth 10000 in
theorem eq_one_of_forall_stabJ_commute (c : F4Mat) (hc : isSL c)
    (h : ∀ g : F4Mat, stabJ g → c * g = g * c) : c = 1 := by
  revert c
  decide

set_option maxRecDepth 10000 in
theorem stabJ_of_forall_stabJ_conj (c : F4Mat) (hc : isSL c)
    (h : ∀ g : F4Mat, stabJ g → stabJ (c * g * inv2 c)) : stabJ c := by
  revert c
  decide

@[expose] def mkSL (g : F4Mat) (hg : isSL g) : SL(2, F4) := ⟨g, hg⟩

abbrev StabJ (g : SL(2, F4)) : Prop := stabJ g.1

def stabJEquiv : {g : SL(2, F4) // StabJ g} ≃ {g : F4Mat // stabJ g} where
  toFun g := ⟨g.1.1, g.2⟩
  invFun g := ⟨⟨g.1, g.2.1⟩, g.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl

theorem card_stabJ_SL : Nat.card {g : SL(2, F4) // StabJ g} = 6 := by
  rw [Nat.card_congr stabJEquiv, card_stabJ]

theorem eq_zero_or_eq_J_of_forall_StabJ (Y : F4Mat) (hY : (Y.map frob)ᵀ = Y)
    (hfix : ∀ g : SL(2, F4), StabJ g → Act g.1 Y = Y) : Y = 0 ∨ Y = J := by
  apply eq_zero_or_eq_J_of_forall_stabJ Y hY
  intro g hg
  exact hfix (mkSL g hg.1) hg

theorem eq_one_of_forall_StabJ_commute (c : SL(2, F4))
    (h : ∀ g : SL(2, F4), StabJ g → c * g = g * c) : c = 1 := by
  apply Subtype.ext
  apply eq_one_of_forall_stabJ_commute c.1 c.2
  intro g hg
  exact congrArg Subtype.val (h (mkSL g hg.1) hg)

theorem StabJ_of_forall_StabJ_conj (c : SL(2, F4))
    (h : ∀ g : SL(2, F4), StabJ g → StabJ (c * g * c⁻¹)) : StabJ c := by
  apply stabJ_of_forall_stabJ_conj c.1 c.2
  intro g hg
  have hthis := h (mkSL g hg.1) hg
  have hcoe : (c * mkSL g hg.1 * c⁻¹).1 = c.1 * g * inv2 c.1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_inv_eq_inv2]
    rfl
  simpa [StabJ, hcoe] using hthis

end CFSG.GF2Type.Smith1979.W4Swap.Model
