module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5sh8_d8_not_comm {X : Type} [Group X] (P : Subgroup X)
    (hP : Nonempty (↥P ≃* DihedralGroup 4)) : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  obtain ⟨φ⟩ := hP
  by_contra h
  push_neg at h
  have hcomm : ∀ x y : DihedralGroup 4, x * y = y * x := by
    intro x y
    have hxy : φ.symm x * φ.symm y = φ.symm y * φ.symm x :=
      Subtype.ext (by simpa using h (φ.symm x) (φ.symm x).2 (φ.symm y) (φ.symm y).2)
    simpa using congrArg φ hxy
  exact DihedralGroup.not_commutative (n := 4) (by decide) (by decide)
    (IsMulCommutative.of_comm hcomm)

end CFSG.OddStandard.SmallF3.Omega
