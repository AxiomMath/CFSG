module

public import CFSG.LinearAlgebra.RootGroupSL.FpfTwo
public import CFSG.LinearAlgebra.RootGroupSL.FpfOne

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]

variable [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

theorem exists_fpf
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X)) :
    ∃ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      Odd (orderOf h) ∧
      Subgroup.centralizer ({h} : Set (SpecialLinearGroup k (DSpace E X))) ⊓ QK k E X =
        rootSL k E X := by
  rcases hstar with hd | ⟨hd, hk, hX⟩
  · exact exists_fpf_of_two_le_finrank hd
  · exact exists_fpf_of_finrank_eq_one hd hk hX

end CFSG.LinearAlgebra.RootGroupSL
