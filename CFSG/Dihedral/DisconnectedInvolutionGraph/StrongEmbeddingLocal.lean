module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbedding

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

theorem stronglyEmbedded_intersection_no_involution (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) (g : G) (houtside : g ∉ subgroup)
    (element : G) (horder : orderOf element = 2) :
    element ∉ subgroup ⊓ conjugateSubgroup subgroup g := by
  intro hmem
  have hdiv := (subgroup ⊓ conjugateSubgroup subgroup g).orderOf_dvd_natCard hmem
  rw [horder] at hdiv
  exact (Nat.not_even_iff_odd.mpr (hstrong.2.2 g houtside))
    (even_iff_two_dvd.mpr hdiv)

theorem stronglyEmbedded_even_subgroup_normalizer_le (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) (smaller : Subgroup G)
    (hle : smaller ≤ subgroup) (heven : Even (Nat.card smaller)) :
    Subgroup.normalizer (smaller : Set G) ≤ subgroup := by
  intro g hnormalizes
  by_contra houtside
  have hintersection : smaller ≤ subgroup ⊓ conjugateSubgroup subgroup g := by
    intro element hmem
    refine ⟨hle hmem, ?_⟩
    have hconjmem := (Subgroup.mem_normalizer_iff''.mp hnormalizes element).mp hmem
    change (MulAut.conj g⁻¹) element ∈ subgroup
    simpa using hle hconjmem
  have hdiv := (even_iff_two_dvd.mp heven).trans
    (Subgroup.card_dvd_of_le hintersection)
  exact (Nat.not_even_iff_odd.mpr (hstrong.2.2 g houtside))
    (even_iff_two_dvd.mpr hdiv)

theorem stronglyEmbedded_self_normalizing (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) :
    Subgroup.normalizer (subgroup : Set G) = subgroup := by
  exact le_antisymm
    (stronglyEmbedded_even_subgroup_normalizer_le subgroup hstrong subgroup le_rfl hstrong.2.1)
    Subgroup.le_normalizer

end CFSG.DisconnectedInvolutionGraph.Helpers
