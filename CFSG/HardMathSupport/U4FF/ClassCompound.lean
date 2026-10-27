module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix

@[expose] def pair6 : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

@[expose] def sortPair (x y : Fin 4) : Fin 4 × Fin 4 :=
  if x < y then (x, y) else (y, x)

@[expose] def compound2 {R : Type*} [CommRing R] (g : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun I J =>
    g (pair6 I).1 (pair6 J).1 * g (pair6 I).2 (pair6 J).2 -
      g (pair6 I).1 (pair6 J).2 * g (pair6 I).2 (pair6 J).1

@[expose] def deriv2 (i j : Fin 4) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun I J =>
    if i ≠ (pair6 J).1 ∧ i ≠ (pair6 J).2 ∧
        ((j = (pair6 J).1 ∧ pair6 I = sortPair i (pair6 J).2) ∨
          (j = (pair6 J).2 ∧ pair6 I = sortPair (pair6 J).1 i))
    then 1 else 0

theorem compound2_mul {R : Type*} [CommRing R] (g h : Matrix (Fin 4) (Fin 4) R) :
    compound2 (g * h) = compound2 g * compound2 h := by
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [compound2, pair6, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_six] <;> ring

theorem compound2_one {R : Type*} [CommRing R] :
    compound2 (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  ext I J
  fin_cases I <;> fin_cases J <;> simp [compound2, pair6, Matrix.one_apply]

theorem compound2_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (g : Matrix (Fin 4) (Fin 4) R) : compound2 (g.map φ) = (compound2 g).map φ := by
  ext I J
  simp [compound2, Matrix.map_apply]

theorem compound2_transvection_row0 {k : Type*} [Field k] [CharP k 2] (j : Fin 4)
    (hij : (0 : Fin 4) ≠ j) (a : k) :
    compound2 (1 + Matrix.single 0 j a) =
      1 + a • (deriv2 0 j).map (ZMod.castHom (dvd_refl 2) k) := by
  ext I J
  fin_cases j <;> try exact absurd rfl hij
  all_goals
    fin_cases I <;> fin_cases J <;>
      simp [compound2, deriv2, sortPair, pair6, Matrix.single_apply, Matrix.one_apply,
        CharTwo.neg_eq, CharTwo.sub_eq_add]

theorem compound2_transvection_row1 {k : Type*} [Field k] [CharP k 2] (j : Fin 4)
    (hij : (1 : Fin 4) ≠ j) (a : k) :
    compound2 (1 + Matrix.single 1 j a) =
      1 + a • (deriv2 1 j).map (ZMod.castHom (dvd_refl 2) k) := by
  ext I J
  fin_cases j <;> try exact absurd rfl hij
  all_goals
    fin_cases I <;> fin_cases J <;>
      simp [compound2, deriv2, sortPair, pair6, Matrix.single_apply, Matrix.one_apply,
        CharTwo.neg_eq, CharTwo.sub_eq_add]

theorem compound2_transvection_row2 {k : Type*} [Field k] [CharP k 2] (j : Fin 4)
    (hij : (2 : Fin 4) ≠ j) (a : k) :
    compound2 (1 + Matrix.single 2 j a) =
      1 + a • (deriv2 2 j).map (ZMod.castHom (dvd_refl 2) k) := by
  ext I J
  fin_cases j <;> try exact absurd rfl hij
  all_goals
    fin_cases I <;> fin_cases J <;>
      simp [compound2, deriv2, sortPair, pair6, Matrix.single_apply, Matrix.one_apply,
        CharTwo.neg_eq, CharTwo.sub_eq_add]

theorem compound2_transvection_row3 {k : Type*} [Field k] [CharP k 2] (j : Fin 4)
    (hij : (3 : Fin 4) ≠ j) (a : k) :
    compound2 (1 + Matrix.single 3 j a) =
      1 + a • (deriv2 3 j).map (ZMod.castHom (dvd_refl 2) k) := by
  ext I J
  fin_cases j <;> try exact absurd rfl hij
  all_goals
    fin_cases I <;> fin_cases J <;>
      simp [compound2, deriv2, sortPair, pair6, Matrix.single_apply, Matrix.one_apply,
        CharTwo.neg_eq, CharTwo.sub_eq_add]

theorem compound2_transvection {k : Type*} [Field k] [CharP k 2] (i j : Fin 4) (hij : i ≠ j)
    (a : k) :
    compound2 (1 + Matrix.single i j a) =
      1 + a • (deriv2 i j).map (ZMod.castHom (dvd_refl 2) k) := by
  fin_cases i
  · exact compound2_transvection_row0 j hij a
  · exact compound2_transvection_row1 j hij a
  · exact compound2_transvection_row2 j hij a
  · exact compound2_transvection_row3 j hij a

end CFSG.HardMathSupport.U4FF
