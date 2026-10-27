module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5pe8s_aut_eq_one_of_two_group {Y : Type} [Group Y] (P : Sylow 2 Y)
    (hP : (P : Subgroup Y) = ⊤) (κ : MulAut Y) (hfix : ∀ x ∈ (P : Subgroup Y), κ x = x) :
    κ = 1 := by
  ext x
  rw [hfix x (by rw [hP]; exact Subgroup.mem_top x), MulAut.one_apply]

end CFSG.OddStandard.SmallF3.Omega
