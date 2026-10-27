module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8STwo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8SA7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8SS4
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5pe8_small {Y : Type} [Group Y] [Finite Y] (P : Sylow 2 Y)
    (hP : Nonempty (↥P ≃* DihedralGroup 4))
    (hshape : (P : Subgroup Y) = ⊤ ∨ Nonempty (Y ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (Y ≃* Equiv.Perm (Fin 4)))
    (κ : MulAut Y) (hodd : Odd (orderOf κ)) (hfix : ∀ x ∈ (P : Subgroup Y), κ x = x) :
    κ = 1 := by
  rcases hshape with h | h | h
  · exact sec5pe8s_aut_eq_one_of_two_group P h κ hfix
  · obtain ⟨e⟩ := h
    exact sec5pe8s_aut_eq_one_of_alt7 P e κ hodd hfix
  · obtain ⟨e⟩ := h
    exact sec5pe8s_aut_eq_one_of_perm_four P e κ hodd hfix

end CFSG.OddStandard.SmallF3.Omega
