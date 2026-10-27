module

public import CFSG.CharacterTheory.Semidihedral.DihedralNormalIndex

public section

namespace CFSG.Semidihedral.Principal

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem noncyclic_normal_dihedral_subgroup_fills_index_two_part (S : Sylow 2 Γ) {k : ℕ}
    (hk : 2 ≤ k) (hS : Nonempty (DihedralGroup (2 ^ (k - 1)) ≃* (S : Subgroup Γ)))
    (L : Subgroup Γ) [L.Normal] (J : Subgroup Γ) (hJ : J.index = 2) (hLJ : L ≤ J)
    (hL : ∃ P : Sylow 2 L, ¬ IsCyclic (P : Subgroup L)) :
    3 ≤ k ∧ (S : Subgroup Γ) ⊓ L = (S : Subgroup Γ) ⊓ J ∧ L.relIndex (S : Subgroup Γ) = 2 ∧
      Odd (L.relIndex J) ∧
      Nonempty (((S : Subgroup Γ) ⊓ L : Subgroup Γ) ≃* DihedralGroup (2 ^ (k - 2))) ∧
      ∃ m, Odd m ∧ L.index = 2 * m := by
  obtain ⟨e⟩ := hS
  obtain ⟨T, hT⟩ := hL
  obtain ⟨hk3, hSL, hrel, hodd, hdihedral, -, -⟩ :=
    CFSG.Semidihedral.DihedralNormalIndex.noncyclic_normal_dihedral_fills_index_two k hk S e.symm
      L inferInstance J hJ hLJ T hT
  refine ⟨hk3, hSL, ?_, hodd, hdihedral, L.relIndex J, hodd, ?_⟩
  · rw [← Subgroup.inf_relIndex_left]
    exact hrel
  · rw [← Subgroup.relIndex_mul_index hLJ, hJ, mul_comm]

end CFSG.Semidihedral.Principal
