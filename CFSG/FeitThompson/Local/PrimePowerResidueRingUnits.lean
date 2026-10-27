module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p e : ℕ}

theorem isUnit_iff_castHom_ne_zero (hp : p.Prime) (he : e ≠ 0) (x : ZMod (p ^ e)) :
    IsUnit x ↔ ZMod.castHom (dvd_pow_self p he) (ZMod p) x ≠ 0 := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp (Nat.pos_of_ne_zero he), map_natCast, Ne,
    ZMod.natCast_eq_zero_iff]

theorem isUnit_iff_isUnit_castHom (hp : p.Prime) (he : e ≠ 0) (x : ZMod (p ^ e)) :
    IsUnit x ↔ IsUnit (ZMod.castHom (dvd_pow_self p he) (ZMod p) x) := by
  have := Fact.mk hp
  rw [isUnit_iff_castHom_ne_zero hp he, isUnit_iff_ne_zero]

theorem isUnit_matrix_iff_isUnit_mapMatrix (hp : p.Prime) (he : e ≠ 0) {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n (ZMod (p ^ e))) :
    IsUnit A ↔ IsUnit ((ZMod.castHom (dvd_pow_self p he) (ZMod p)).mapMatrix A) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det,
    ← isUnit_iff_isUnit_castHom hp he]

theorem isUnit_matrix_iff_det_mapMatrix_ne_zero (hp : p.Prime) (he : e ≠ 0) {n : Type*}
    [Fintype n] [DecidableEq n] (A : Matrix n n (ZMod (p ^ e))) :
    IsUnit A ↔ ((ZMod.castHom (dvd_pow_self p he) (ZMod p)).mapMatrix A).det ≠ 0 := by
  have := Fact.mk hp
  rw [isUnit_matrix_iff_isUnit_mapMatrix hp he, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

end CFSG.FeitThompson
