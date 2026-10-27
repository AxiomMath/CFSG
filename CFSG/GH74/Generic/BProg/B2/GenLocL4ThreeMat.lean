module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutMix
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Matrix
open scoped MatrixGroups

namespace GenLocL4ThreeMat

open GenLocL4Out

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 3)

@[expose] def xSL (i j : Fin 4) (h : i ≠ j) : SL(4, ZMod 3) := tv i j h 1

@[expose] def x01 : SL(4, ZMod 3) := xSL 0 1 (by decide)
@[expose] def x02 : SL(4, ZMod 3) := xSL 0 2 (by decide)
@[expose] def x03 : SL(4, ZMod 3) := xSL 0 3 (by decide)
@[expose] def x10 : SL(4, ZMod 3) := xSL 1 0 (by decide)
@[expose] def x12 : SL(4, ZMod 3) := xSL 1 2 (by decide)
@[expose] def x13 : SL(4, ZMod 3) := xSL 1 3 (by decide)
@[expose] def x20 : SL(4, ZMod 3) := xSL 2 0 (by decide)
@[expose] def x21 : SL(4, ZMod 3) := xSL 2 1 (by decide)
@[expose] def x23 : SL(4, ZMod 3) := xSL 2 3 (by decide)
@[expose] def x30 : SL(4, ZMod 3) := xSL 3 0 (by decide)
@[expose] def x31 : SL(4, ZMod 3) := xSL 3 1 (by decide)
@[expose] def x32 : SL(4, ZMod 3) := xSL 3 2 (by decide)

@[expose] def tM : M4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
@[expose] def jM : M4 := !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]
@[expose] def BjM : M4 := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]

section Mem

variable {Γ : Subgroup SL(4, ZMod 3)} {a b c e y : SL(4, ZMod 3)}

theorem mem_of_coe_eq (ha : a ∈ Γ) (h : (y : M4) = a) : y ∈ Γ := by
  rwa [show y = a from Subtype.ext h]

theorem mem_of_coe_mul (ha : a ∈ Γ) (hb : b ∈ Γ) (h : (y : M4) = a * b) : y ∈ Γ :=
  mem_of_coe_eq (Γ.mul_mem ha hb) (by rw [h, Matrix.SpecialLinearGroup.coe_mul])

theorem mem_of_coe_mul3 (ha : a ∈ Γ) (hb : b ∈ Γ) (hc : c ∈ Γ) (h : (y : M4) = a * b * c) : y ∈ Γ :=
  mem_of_coe_eq (Γ.mul_mem (Γ.mul_mem ha hb) hc)
    (by rw [h, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul])

theorem coe_list_prod (L : List SL(4, ZMod 3)) :
    ((L.prod : SL(4, ZMod 3)) : M4) = (L.map fun g => (g : M4)).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.prod_cons, ih]

theorem mem_of_conj {r x q : SL(4, ZMod 3)} (hr : r ∈ Γ) (hx : x ∈ Γ) (h : (r : M4) * x = q * r) : q ∈ Γ :=
  mem_of_conj_eq hr hx (Subtype.ext (by simpa only [Matrix.SpecialLinearGroup.coe_mul] using h))

theorem mem_of_coe_prod (L : List SL(4, ZMod 3)) (hL : ∀ g ∈ L, g ∈ Γ)
    (h : (y : M4) = (L.map fun g => (g : M4)).prod) : y ∈ Γ :=
  mem_of_coe_eq (Subgroup.list_prod_mem Γ hL) (by rw [h, coe_list_prod])

end Mem

theorem top_of_root_elements (Γ : Subgroup SL(4, ZMod 3)) (h : ∀ (i j : Fin 4) (hij : i ≠ j), tv i j hij 1 ∈ Γ) :
    Γ = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 4) (K := ZMod 3)]
  refine (Subgroup.closure_le Γ).2 ?_
  rintro _ ⟨i, j, hij, c, rfl⟩
  have key : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  show tv i j hij c ∈ Γ
  rcases key c with rfl | rfl | rfl
  · have h0 : tv i j hij (0 : ZMod 3) = 1 := Subtype.ext (by simp [coe_tv])
    rw [h0]
    exact Γ.one_mem
  · exact h i j hij
  · have h2 := tv_mul i j hij (1 : ZMod 3) 1
    rw [one_add_one_eq_two] at h2
    rw [← h2]
    exact Γ.mul_mem (h i j hij) (h i j hij)

theorem top_of_root_elements' (Γ : Subgroup SL(4, ZMod 3)) (h01 : x01 ∈ Γ) (h02 : x02 ∈ Γ) (h03 : x03 ∈ Γ)
    (h10 : x10 ∈ Γ) (h12 : x12 ∈ Γ) (h13 : x13 ∈ Γ) (h20 : x20 ∈ Γ) (h21 : x21 ∈ Γ) (h23 : x23 ∈ Γ)
    (h30 : x30 ∈ Γ) (h31 : x31 ∈ Γ) (h32 : x32 ∈ Γ) : Γ = ⊤ := by
  refine top_of_root_elements Γ fun i j hij => ?_
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01 | exact h02 | exact h03 | exact h10 | exact h12 | exact h13
    | exact h20 | exact h21 | exact h23 | exact h30 | exact h31 | exact h32

end GenLocL4ThreeMat

end CFSG.GH74.Generic.BProg.B2
