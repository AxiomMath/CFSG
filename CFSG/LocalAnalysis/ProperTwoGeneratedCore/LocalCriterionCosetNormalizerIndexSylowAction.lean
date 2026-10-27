module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe v w t

variable {A : Type v} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

theorem sylow_isPretransitive_of_primePower_card
    {X : Type t} [MulAction A X] [Finite X] [MulAction.IsPretransitive A X]
    (hcard : ∃ e : ℕ, Nat.card X = p ^ e) (S : Sylow p A) :
    MulAction.IsPretransitive (S : Subgroup A) X := by
  obtain ⟨e, he⟩ := hcard
  constructor
  intro x y
  have hindex : (MulAction.stabilizer A x).index = p ^ e := by
    rw [MulAction.index_stabilizer_of_transitive, he]
  have hS := sylow_relIndex_eq_of_primePower_index
    (MulAction.stabilizer A x) ⟨e, hindex⟩ S
  have horbit : (MulAction.orbit (S : Subgroup A) x).ncard = Nat.card X := by
    rw [Subgroup.relIndex, MulAction.stabilizer_subgroupOf,
      MulAction.index_stabilizer, MulAction.index_stabilizer_of_transitive] at hS
    exact hS
  have hfull : MulAction.orbit (S : Subgroup A) x = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    simpa only [Set.ncard_univ] using horbit.ge
  apply MulAction.mem_orbit_iff.mp
  rw [hfull]
  exact Set.mem_univ y

variable {B : Type w} [Group B]

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
