module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

theorem AschbacherHyp.index_commutator_of_le_commutator [Finite C] (hC : AschbacherHyp C Q)
    (hQL : Q ≤ commutator C) : (commutator C).index = 2 := by
  let π : C →* C ⧸ Q := QuotientGroup.mk' Q
  let e : C ⧸ Q ≃* A5WrTwo := hC.quotient.some
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hker : π.ker = Q := QuotientGroup.ker_mk' Q
  have hmapC : (commutator C).map π = commutator (C ⧸ Q) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hπ]
    rfl
  have hindexC : ((commutator C).map π).index = (commutator C).index :=
    Subgroup.index_map_eq (H := commutator C) (f := π) hπ (by rw [hker]; exact hQL)
  have hmape : (commutator (C ⧸ Q)).map (e : C ⧸ Q →* A5WrTwo) = commutator A5WrTwo := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (e : C ⧸ Q →* A5WrTwo) e.surjective]
    rfl
  calc (commutator C).index
      = ((commutator C).map π).index := hindexC.symm
    _ = (commutator (C ⧸ Q)).index := by rw [hmapC]
    _ = ((commutator (C ⧸ Q)).map (e : C ⧸ Q →* A5WrTwo)).index :=
          (Subgroup.index_map_equiv (H := commutator (C ⧸ Q)) e).symm
    _ = (commutator A5WrTwo).index := by rw [hmape]
    _ = 2 := A5WrTwo.index_commutator

end CFSG.EvenSporadicStandard.HNRecog
