module
public import CFSG.FeitThompson.Local.PrimePowerResidueRingUnits
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p e : ℕ}

theorem castHom_comp_castHom_pow_succ (he : e ≠ 0) :
    (ZMod.castHom (dvd_pow_self p he) (ZMod p)).comp
        (ZMod.castHom (pow_dvd_pow p e.le_succ) (ZMod (p ^ e)))
      = ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero e)) (ZMod p) :=
  ZMod.castHom_comp _ _

theorem generalLinearGroup_map_castHom_surjective (hp : p.Prime) (he : e ≠ 0) {n : Type*}
    [Fintype n] [DecidableEq n] :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := n)
      (ZMod.castHom (pow_dvd_pow p e.le_succ) (ZMod (p ^ e)))) := by
  intro B
  obtain ⟨g, hg⟩ := (ZMod.castHom_surjective (pow_dvd_pow p e.le_succ)).hasRightInverse
  set f := ZMod.castHom (pow_dvd_pow p e.le_succ) (ZMod (p ^ e)) with hf
  set A : Matrix n n (ZMod (p ^ (e + 1))) := (B.val).map g with hAdef
  have hA : f.mapMatrix A = B.val := by
    ext i j
    simpa [hAdef, RingHom.mapMatrix_apply] using hg (B.val i j)
  have hu : IsUnit A := by
    rw [isUnit_matrix_iff_isUnit_mapMatrix hp (Nat.succ_ne_zero e)]
    have h1 : (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero e)) (ZMod p)).mapMatrix A
        = (ZMod.castHom (dvd_pow_self p he) (ZMod p)).mapMatrix (f.mapMatrix A) := by
      rw [← RingHom.comp_apply, RingHom.mapMatrix_comp, hf, castHom_comp_castHom_pow_succ he]
    rw [h1, hA, ← isUnit_matrix_iff_isUnit_mapMatrix hp he]
    exact B.isUnit
  refine ⟨hu.unit, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.val_map_apply]
  simpa [IsUnit.unit_spec, RingHom.mapMatrix_apply] using hA

theorem exists_generalLinearGroup_castHom_entry_eq (hp : p.Prime) (he : e ≠ 0) {n : Type*}
    [Fintype n] [DecidableEq n] (B : Matrix.GeneralLinearGroup n (ZMod (p ^ e))) :
    ∃ A : Matrix.GeneralLinearGroup n (ZMod (p ^ (e + 1))), ∀ i j,
      ZMod.castHom (pow_dvd_pow p e.le_succ) (ZMod (p ^ e)) (A i j) = B i j := by
  obtain ⟨A, hA⟩ := generalLinearGroup_map_castHom_surjective (n := n) hp he B
  exact ⟨A, fun i j => by rw [← Matrix.GeneralLinearGroup.map_apply, hA]⟩

theorem generalLinearGroup_map_castHom_range (hp : p.Prime) (he : e ≠ 0) {n : Type*}
    [Fintype n] [DecidableEq n] :
    (Matrix.GeneralLinearGroup.map (n := n)
      (ZMod.castHom (pow_dvd_pow p e.le_succ) (ZMod (p ^ e)))).range = ⊤ :=
  MonoidHom.range_eq_top.2 (generalLinearGroup_map_castHom_surjective hp he)

end CFSG.FeitThompson
