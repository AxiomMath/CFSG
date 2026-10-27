module

public import CFSG.CharacterTheory.Semidihedral.FieldInterface
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerDegreeProduct

public section

namespace CFSG.Semidihedral.SimpleLayerFrontier

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem sylow_two_not_cyclic_of_dihedral {L : Type*} [Group L] [Finite L] (m : ℕ) (hm : 2 ≤ m)
    (U : Sylow 2 L) (hU : Nonempty (U ≃* DihedralGroup (2 ^ (m - 1)))) :
    ∀ V : Sylow 2 L, ¬ IsCyclic V := by
  intro V hV
  obtain ⟨e⟩ := hU
  have h1 : 2 ^ (m - 1) ≠ 1 :=
    (Nat.one_lt_pow (by omega : m - 1 ≠ 0) (by norm_num : 1 < 2)).ne'
  have hUc : IsCyclic U := (Sylow.equiv V U).isCyclic.mp hV
  exact DihedralGroup.not_isCyclic h1 (e.isCyclic.mp hUc)

theorem frontier_layer_setup
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (m : ℕ) (hm : 2 ≤ m) (U : Sylow 2 (CFSG.generalizedFitting (Gamma t)))
    (hU : Nonempty (U ≃* DihedralGroup (2 ^ (m - 1)))) :
    (∀ V : Subgroup G, V.index ≠ 2) ∧
    (∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic V) ∧
    CFSG.generalizedFitting (Gamma t) ≤ J t ∧
    ¬ Nonempty (CFSG.generalizedFitting (Gamma t) ≃* alternatingGroup (Fin 7)) ∧
    ∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f := by
  have hG : ∀ V : Subgroup G, V.index ≠ 2 :=
    CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨-, hJindex, -, -, -, ⟨P, ⟨eP⟩⟩, -⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  have hLJ : CFSG.generalizedFitting (Gamma t) ≤ J t :=
    simple_le_index_two _ _ hJindex hnonab
  have hnot7 :=
    AlternatingSevenExclusion.dihedral_index_two_excludes_alternating_seven_layer
      hnonab P (n - 1) (by omega)
      (by
        rw [show n - 1 - 1 = n - 2 by omega]
        exact eP)
      (J t) hJindex hLJ
  refine ⟨hG, sylow_two_not_cyclic_of_dihedral m hm U hU, hLJ, hnot7, ?_⟩
  rcases CFSG.Milestones.lr_dihedral_simple_recognition (CFSG.generalizedFitting (Gamma t))
      hnonab U m hm hU with hfield | h7
  · obtain ⟨p, f, hp, hp2, hf, hmodel⟩ := hfield
    exact ⟨p, f, hp, hp.odd_of_ne_two hp2, hf,
      FieldInterface.psl_two_field_size_ge_five hp hp2 hf hmodel, hmodel⟩
  · exact (hnot7 h7).elim

end CFSG.Semidihedral.SimpleLayerFrontier
