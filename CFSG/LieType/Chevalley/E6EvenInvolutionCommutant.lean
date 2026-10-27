module

public import Mathlib.Data.Matrix.Basis

public section

namespace CFSG.LieType.Chevalley.E6EvenInvolution

open Matrix

variable (R : Type*) [CommRing R]

abbrev E (a b : Fin 6) : Matrix (Fin 6) (Fin 6) R := single a b 1

@[expose] def nMat1 : Matrix (Fin 6) (Fin 6) R := E R 0 1

@[expose] def nMat2 : Matrix (Fin 6) (Fin 6) R := E R 0 1 + E R 4 5

@[expose] def nMat3 : Matrix (Fin 6) (Fin 6) R := E R 0 1 + E R 2 3 + E R 4 5

variable {R} {B : Matrix (Fin 6) (Fin 6) R}

theorem E_mul_E (a b c d : Fin 6) : E R a b * E R c d = if b = c then E R a d else 0 := by
  split_ifs with h
  · subst h
    rw [single_mul_single_same, mul_one]
  · exact single_mul_single_of_ne _ _ _ _ h _

theorem col_eq_zero {a b : Fin 6} (h : B * single a b 1 = single a b 1 * B) {i : Fin 6}
    (hi : i ≠ a) : B i a = 0 := by
  have e := congrFun (congrFun h i) b
  rwa [mul_single_apply_same, single_mul_apply_of_ne (h := hi), mul_one] at e

theorem row_eq_zero {a b : Fin 6} (h : B * single a b 1 = single a b 1 * B) {j : Fin 6}
    (hj : j ≠ b) : B b j = 0 := by
  have e := congrFun (congrFun h a) j
  rw [mul_single_apply_of_ne (hbj := hj), single_mul_apply_same, one_mul] at e
  exact e.symm

theorem diag_eq {a b : Fin 6} (h : B * single a b 1 = single a b 1 * B) : B a a = B b b := by
  have e := congrFun (congrFun h a) b
  rwa [mul_single_apply_same, single_mul_apply_same, mul_one, one_mul] at e

section Pair

variable {x y z w : Fin 6}
  (h : B * (single x y 1 + single z w 1) = (single x y 1 + single z w 1) * B)
include h

theorem pair_entry (i j : Fin 6) :
    (B * E R x y) i j + (B * E R z w) i j = (E R x y * B) i j + (E R z w * B) i j := by
  have e := congrFun (congrFun h i) j
  rwa [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.add_apply] at e

theorem pair_xz (hxz : x ≠ z) (hwy : w ≠ y) : B x z = B y w := by
  have e := pair_entry h x w
  rwa [mul_single_apply_of_ne (hbj := hwy), mul_single_apply_same, single_mul_apply_same,
    single_mul_apply_of_ne (h := hxz), zero_add, add_zero, mul_one, one_mul] at e

theorem pair_zx (hxz : x ≠ z) (hwy : w ≠ y) : B z x = B w y := by
  have e := pair_entry h z y
  rwa [mul_single_apply_same, mul_single_apply_of_ne (hbj := hwy.symm),
    single_mul_apply_of_ne (h := hxz.symm), single_mul_apply_same, add_zero, zero_add, mul_one,
    one_mul] at e

theorem pair_colx {i : Fin 6} (hix : i ≠ x) (hiz : i ≠ z) (hwy : w ≠ y) : B i x = 0 := by
  have e := pair_entry h i y
  rwa [mul_single_apply_same, mul_single_apply_of_ne (hbj := hwy.symm),
    single_mul_apply_of_ne (h := hix), single_mul_apply_of_ne (h := hiz), add_zero, add_zero,
    mul_one] at e

theorem pair_colz {i : Fin 6} (hix : i ≠ x) (hiz : i ≠ z) (hwy : w ≠ y) : B i z = 0 := by
  have e := pair_entry h i w
  rwa [mul_single_apply_of_ne (hbj := hwy), mul_single_apply_same,
    single_mul_apply_of_ne (h := hix), single_mul_apply_of_ne (h := hiz), zero_add, add_zero,
    mul_one] at e

theorem pair_rowy {j : Fin 6} (hjy : j ≠ y) (hjw : j ≠ w) (hxz : x ≠ z) : B y j = 0 := by
  have e := pair_entry h x j
  rw [mul_single_apply_of_ne (hbj := hjy), mul_single_apply_of_ne (hbj := hjw),
    single_mul_apply_same, single_mul_apply_of_ne (h := hxz), add_zero, add_zero, one_mul] at e
  exact e.symm

theorem pair_roww {j : Fin 6} (hjy : j ≠ y) (hjw : j ≠ w) (hxz : x ≠ z) : B w j = 0 := by
  have e := pair_entry h z j
  rw [mul_single_apply_of_ne (hbj := hjy), mul_single_apply_of_ne (hbj := hjw),
    single_mul_apply_of_ne (h := hxz.symm), single_mul_apply_same, add_zero, zero_add,
    one_mul] at e
  exact e.symm

theorem pair_diagx (hxz : x ≠ z) (hwy : w ≠ y) : B x x = B y y := by
  have e := pair_entry h x y
  rwa [mul_single_apply_same, mul_single_apply_of_ne (hbj := hwy.symm), single_mul_apply_same,
    single_mul_apply_of_ne (h := hxz), add_zero, add_zero, mul_one, one_mul] at e

theorem pair_diagz (hxz : x ≠ z) (hwy : w ≠ y) : B z z = B w w := by
  have e := pair_entry h z w
  rwa [mul_single_apply_of_ne (hbj := hwy), mul_single_apply_same,
    single_mul_apply_of_ne (h := hxz.symm), single_mul_apply_same, zero_add, zero_add, mul_one,
    one_mul] at e

end Pair

theorem commutant1 {R : Type*} [CommRing R] {B : Matrix (Fin 6) (Fin 6) R}
    (h0 : B * E R 0 1 = E R 0 1 * B)
    (h1 : B * E R 2 3 = E R 2 3 * B)
    (h2 : B * E R 3 2 = E R 3 2 * B)
    (h3 : B * E R 4 5 = E R 4 5 * B)
    (h4 : B * E R 0 4 = E R 0 4 * B)
    (h5 : B * E R 5 2 = E R 5 2 * B) :
    B = B 0 0 • (1 : Matrix (Fin 6) (Fin 6) R) + B 0 1 • nMat1 R := by
  have f02 : B 0 2 = 0 := (col_eq_zero h1 (i := 0) (by decide))
  have f03 : B 0 3 = 0 := (col_eq_zero h2 (i := 0) (by decide))
  have f04 : B 0 4 = 0 := (col_eq_zero h3 (i := 0) (by decide))
  have f05 : B 0 5 = 0 := (col_eq_zero h5 (i := 0) (by decide))
  have f10 : B 1 0 = 0 := (col_eq_zero h0 (i := 1) (by decide))
  have f11 : B 1 1 = B 0 0 := (diag_eq h0).symm
  have f12 : B 1 2 = 0 := (row_eq_zero h0 (j := 2) (by decide))
  have f13 : B 1 3 = 0 := (row_eq_zero h0 (j := 3) (by decide))
  have f14 : B 1 4 = 0 := (row_eq_zero h0 (j := 4) (by decide))
  have f15 : B 1 5 = 0 := (row_eq_zero h0 (j := 5) (by decide))
  have f20 : B 2 0 = 0 := (col_eq_zero h0 (i := 2) (by decide))
  have f21 : B 2 1 = 0 := (row_eq_zero h2 (j := 1) (by decide))
  have f22 : B 2 2 = B 0 0 := (diag_eq h5).symm |>.trans (diag_eq h3).symm
      |>.trans (diag_eq h4).symm
  have f23 : B 2 3 = 0 := (col_eq_zero h2 (i := 2) (by decide))
  have f24 : B 2 4 = 0 := (row_eq_zero h2 (j := 4) (by decide))
  have f25 : B 2 5 = 0 := (row_eq_zero h2 (j := 5) (by decide))
  have f30 : B 3 0 = 0 := (col_eq_zero h0 (i := 3) (by decide))
  have f31 : B 3 1 = 0 := (row_eq_zero h1 (j := 1) (by decide))
  have f32 : B 3 2 = 0 := (col_eq_zero h1 (i := 3) (by decide))
  have f33 : B 3 3 = B 0 0 := (diag_eq h1).symm |>.trans (diag_eq h5).symm
      |>.trans (diag_eq h3).symm |>.trans (diag_eq h4).symm
  have f34 : B 3 4 = 0 := (row_eq_zero h1 (j := 4) (by decide))
  have f35 : B 3 5 = 0 := (row_eq_zero h1 (j := 5) (by decide))
  have f40 : B 4 0 = 0 := (col_eq_zero h0 (i := 4) (by decide))
  have f41 : B 4 1 = 0 := (row_eq_zero h4 (j := 1) (by decide))
  have f42 : B 4 2 = 0 := (col_eq_zero h1 (i := 4) (by decide))
  have f43 : B 4 3 = 0 := (col_eq_zero h2 (i := 4) (by decide))
  have f44 : B 4 4 = B 0 0 := (diag_eq h4).symm
  have f45 : B 4 5 = 0 := (row_eq_zero h4 (j := 5) (by decide))
  have f50 : B 5 0 = 0 := (col_eq_zero h0 (i := 5) (by decide))
  have f51 : B 5 1 = 0 := (row_eq_zero h3 (j := 1) (by decide))
  have f52 : B 5 2 = 0 := (col_eq_zero h1 (i := 5) (by decide))
  have f53 : B 5 3 = 0 := (col_eq_zero h2 (i := 5) (by decide))
  have f54 : B 5 4 = 0 := (col_eq_zero h3 (i := 5) (by decide))
  have f55 : B 5 5 = B 0 0 := (diag_eq h3).symm |>.trans (diag_eq h4).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, nMat1, f02, f03, f04, f05, f10, f11, f12, f13, f14,
      f15, f20, f21, f22, f23, f24, f25, f30, f31, f32, f33, f34, f35, f40, f41, f42, f43, f44,
      f45, f50, f51, f52, f53, f54, f55]

theorem commutant2 {R : Type*} [CommRing R] {B : Matrix (Fin 6) (Fin 6) R}
    (h0 : B * (E R 0 4 + E R 1 5) = (E R 0 4 + E R 1 5) * B)
    (h1 : B * (E R 4 0 + E R 5 1) = (E R 4 0 + E R 5 1) * B)
    (h2 : B * E R 0 2 = E R 0 2 * B)
    (h3 : B * E R 0 3 = E R 0 3 * B)
    (h4 : B * E R 0 1 = E R 0 1 * B) :
    B = B 0 0 • (1 : Matrix (Fin 6) (Fin 6) R) + B 0 1 • nMat2 R := by
  have f02 : B 0 2 = 0 := (pair_rowy h1 (j := 2) (by decide) (by decide) (by decide))
  have f03 : B 0 3 = 0 := (pair_rowy h1 (j := 3) (by decide) (by decide) (by decide))
  have f04 : B 0 4 = 0 := (pair_colx h1 (i := 0) (by decide) (by decide) (by decide))
  have f05 : B 0 5 = 0 := (pair_colz h1 (i := 0) (by decide) (by decide) (by decide))
  have f10 : B 1 0 = 0 := (col_eq_zero h2 (i := 1) (by decide))
  have f11 : B 1 1 = B 0 0 := (diag_eq h4).symm
  have f12 : B 1 2 = 0 := (pair_roww h1 (j := 2) (by decide) (by decide) (by decide))
  have f13 : B 1 3 = 0 := (pair_roww h1 (j := 3) (by decide) (by decide) (by decide))
  have f14 : B 1 4 = 0 := (pair_colx h1 (i := 1) (by decide) (by decide) (by decide))
  have f15 : B 1 5 = 0 := (pair_colz h1 (i := 1) (by decide) (by decide) (by decide))
  have f20 : B 2 0 = 0 := (pair_colx h0 (i := 2) (by decide) (by decide) (by decide))
  have f21 : B 2 1 = 0 := (pair_colz h0 (i := 2) (by decide) (by decide) (by decide))
  have f22 : B 2 2 = B 0 0 := (diag_eq h2).symm
  have f23 : B 2 3 = 0 := (row_eq_zero h2 (j := 3) (by decide))
  have f24 : B 2 4 = 0 := (pair_colx h1 (i := 2) (by decide) (by decide) (by decide))
  have f25 : B 2 5 = 0 := (pair_colz h1 (i := 2) (by decide) (by decide) (by decide))
  have f30 : B 3 0 = 0 := (pair_colx h0 (i := 3) (by decide) (by decide) (by decide))
  have f31 : B 3 1 = 0 := (pair_colz h0 (i := 3) (by decide) (by decide) (by decide))
  have f32 : B 3 2 = 0 := (row_eq_zero h3 (j := 2) (by decide))
  have f33 : B 3 3 = B 0 0 := (diag_eq h3).symm
  have f34 : B 3 4 = 0 := (pair_colx h1 (i := 3) (by decide) (by decide) (by decide))
  have f35 : B 3 5 = 0 := (pair_colz h1 (i := 3) (by decide) (by decide) (by decide))
  have f40 : B 4 0 = 0 := (pair_colx h0 (i := 4) (by decide) (by decide) (by decide))
  have f41 : B 4 1 = 0 := (pair_colz h0 (i := 4) (by decide) (by decide) (by decide))
  have f42 : B 4 2 = 0 := (pair_rowy h0 (j := 2) (by decide) (by decide) (by decide))
  have f43 : B 4 3 = 0 := (pair_rowy h0 (j := 3) (by decide) (by decide) (by decide))
  have f44 : B 4 4 = B 0 0 := (pair_diagx h0 (by decide) (by decide)).symm
  have f45 : B 4 5 = B 0 1 := (pair_xz h0 (by decide) (by decide)).symm
  have f50 : B 5 0 = 0 := (pair_colx h0 (i := 5) (by decide) (by decide) (by decide))
  have f51 : B 5 1 = 0 := (pair_colz h0 (i := 5) (by decide) (by decide) (by decide))
  have f52 : B 5 2 = 0 := (pair_roww h0 (j := 2) (by decide) (by decide) (by decide))
  have f53 : B 5 3 = 0 := (pair_roww h0 (j := 3) (by decide) (by decide) (by decide))
  have f54 : B 5 4 = 0 := (pair_zx h0 (by decide) (by decide)).symm
      |>.trans (col_eq_zero h2 (i := 1) (by decide))
  have f55 : B 5 5 = B 0 0 := (pair_diagz h0 (by decide) (by decide)).symm
      |>.trans (diag_eq h4).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, nMat2, f02, f03, f04, f05, f10, f11, f12, f13, f14,
      f15, f20, f21, f22, f23, f24, f25, f30, f31, f32, f33, f34, f35, f40, f41, f42, f43, f44,
      f45, f50, f51, f52, f53, f54, f55]

theorem commutant3 {R : Type*} [CommRing R] {B : Matrix (Fin 6) (Fin 6) R}
    (h0 : B * (E R 0 2 + E R 1 3) = (E R 0 2 + E R 1 3) * B)
    (h1 : B * (E R 2 0 + E R 3 1) = (E R 2 0 + E R 3 1) * B)
    (h2 : B * (E R 0 4 + E R 1 5) = (E R 0 4 + E R 1 5) * B)
    (h3 : B * E R 0 1 = E R 0 1 * B) :
    B = B 0 0 • (1 : Matrix (Fin 6) (Fin 6) R) + B 0 1 • nMat3 R := by
  have f02 : B 0 2 = 0 := (pair_colx h1 (i := 0) (by decide) (by decide) (by decide))
  have f03 : B 0 3 = 0 := (pair_colz h1 (i := 0) (by decide) (by decide) (by decide))
  have f04 : B 0 4 = 0 := (pair_rowy h1 (j := 4) (by decide) (by decide) (by decide))
  have f05 : B 0 5 = 0 := (pair_rowy h1 (j := 5) (by decide) (by decide) (by decide))
  have f10 : B 1 0 = 0 := (col_eq_zero h3 (i := 1) (by decide))
  have f11 : B 1 1 = B 0 0 := (diag_eq h3).symm
  have f12 : B 1 2 = 0 := (pair_colx h1 (i := 1) (by decide) (by decide) (by decide))
  have f13 : B 1 3 = 0 := (pair_colz h1 (i := 1) (by decide) (by decide) (by decide))
  have f14 : B 1 4 = 0 := (pair_roww h1 (j := 4) (by decide) (by decide) (by decide))
  have f15 : B 1 5 = 0 := (pair_roww h1 (j := 5) (by decide) (by decide) (by decide))
  have f20 : B 2 0 = 0 := (pair_colx h0 (i := 2) (by decide) (by decide) (by decide))
  have f21 : B 2 1 = 0 := (pair_colz h0 (i := 2) (by decide) (by decide) (by decide))
  have f22 : B 2 2 = B 0 0 := (pair_diagx h0 (by decide) (by decide)).symm
  have f23 : B 2 3 = B 0 1 := (pair_xz h0 (by decide) (by decide)).symm
  have f24 : B 2 4 = 0 := (pair_rowy h0 (j := 4) (by decide) (by decide) (by decide))
  have f25 : B 2 5 = 0 := (pair_rowy h0 (j := 5) (by decide) (by decide) (by decide))
  have f30 : B 3 0 = 0 := (pair_colx h0 (i := 3) (by decide) (by decide) (by decide))
  have f31 : B 3 1 = 0 := (pair_colz h0 (i := 3) (by decide) (by decide) (by decide))
  have f32 : B 3 2 = 0 := (pair_zx h0 (by decide) (by decide)).symm
      |>.trans (col_eq_zero h3 (i := 1) (by decide))
  have f33 : B 3 3 = B 0 0 := (pair_diagz h0 (by decide) (by decide)).symm
      |>.trans (diag_eq h3).symm
  have f34 : B 3 4 = 0 := (pair_roww h0 (j := 4) (by decide) (by decide) (by decide))
  have f35 : B 3 5 = 0 := (pair_roww h0 (j := 5) (by decide) (by decide) (by decide))
  have f40 : B 4 0 = 0 := (pair_colx h0 (i := 4) (by decide) (by decide) (by decide))
  have f41 : B 4 1 = 0 := (pair_colz h0 (i := 4) (by decide) (by decide) (by decide))
  have f42 : B 4 2 = 0 := (pair_colx h1 (i := 4) (by decide) (by decide) (by decide))
  have f43 : B 4 3 = 0 := (pair_colz h1 (i := 4) (by decide) (by decide) (by decide))
  have f44 : B 4 4 = B 0 0 := (pair_diagx h2 (by decide) (by decide)).symm
  have f45 : B 4 5 = B 0 1 := (pair_xz h2 (by decide) (by decide)).symm
  have f50 : B 5 0 = 0 := (pair_colx h0 (i := 5) (by decide) (by decide) (by decide))
  have f51 : B 5 1 = 0 := (pair_colz h0 (i := 5) (by decide) (by decide) (by decide))
  have f52 : B 5 2 = 0 := (pair_colx h1 (i := 5) (by decide) (by decide) (by decide))
  have f53 : B 5 3 = 0 := (pair_colz h1 (i := 5) (by decide) (by decide) (by decide))
  have f54 : B 5 4 = 0 := (pair_zx h2 (by decide) (by decide)).symm
      |>.trans (col_eq_zero h3 (i := 1) (by decide))
  have f55 : B 5 5 = B 0 0 := (pair_diagz h2 (by decide) (by decide)).symm
      |>.trans (diag_eq h3).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, nMat3, f02, f03, f04, f05, f10, f11, f12, f13, f14,
      f15, f20, f21, f22, f23, f24, f25, f30, f31, f32, f33, f34, f35, f40, f41, f42, f43, f44,
      f45, f50, f51, f52, f53, f54, f55]

end CFSG.LieType.Chevalley.E6EvenInvolution
