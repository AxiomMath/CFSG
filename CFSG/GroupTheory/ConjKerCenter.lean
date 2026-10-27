module

public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem ker_conj_eq_center {G : Type*} [Group G] :
    (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h y
    have h1 := congrArg (fun φ : MulAut G => φ y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    have h2 : (x * y * x⁻¹) * x = x * y := by group
    rw [← h2, h1]
  · intro h
    ext y
    rw [MulAut.conj_apply, (h y).symm]
    simp

end CFSG.GroupTheory
