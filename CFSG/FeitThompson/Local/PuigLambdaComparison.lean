module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {X : Type*} [Group X] {Z : Type*} [Group Z]

theorem map_puigLambda_le_puigLambda_map (f : X →* Z) (U : Subgroup X) :
    (puigLambda U).map f ≤ puigLambda (U.map f) := by
  rw [map_le_iff_le_comap]
  refine puigLambda_le fun A hA hU => ?_
  rw [← map_le_iff_le_comap]
  have hU' : ∀ u ∈ U, ∀ a ∈ A, u * a * u⁻¹ ∈ A := fun u hu a ha =>
    (mem_normalizer_iff.1 (hU hu) a).1 ha
  refine le_puigLambda (map_isMulCommutative A f) ?_
  rintro y ⟨u, hu, rfl⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨u * a * u⁻¹, hU' u hu a ha, by simp⟩
  · rintro ⟨a, ha, hEq⟩
    refine ⟨u⁻¹ * a * u⁻¹⁻¹, hU' u⁻¹ (inv_mem hu) a ha, ?_⟩
    simp only [map_mul, map_inv, hEq]
    group

theorem map_puigLambda_subgroupOf_le_puigLambda {Y U : Subgroup X} (hU : U ≤ Y) :
    (puigLambda (U.subgroupOf Y)).map Y.subtype ≤ puigLambda U := by
  have h := map_puigLambda_le_puigLambda_map Y.subtype (U.subgroupOf Y)
  rwa [map_subgroupOf_eq_of_le hU] at h

theorem puigLambda_subgroupOf_le_subgroupOf {Y U : Subgroup X} (hU : U ≤ Y) :
    puigLambda (U.subgroupOf Y) ≤ (puigLambda U).subgroupOf Y :=
  map_le_iff_le_comap.1 (map_puigLambda_subgroupOf_le_puigLambda hU)

theorem iSup_le_puigLambda {U : Subgroup X} {ι : Sort*} {A : ι → Subgroup X}
    (hab : ∀ i, IsMulCommutative (A i)) (hnorm : ∀ i, U ≤ normalizer (A i : Set X)) :
    ⨆ i, A i ≤ puigLambda U :=
  iSup_le fun i => le_puigLambda (hab i) (hnorm i)

theorem sSup_le_puigLambda {U : Subgroup X} {S : Set (Subgroup X)}
    (hab : ∀ A ∈ S, IsMulCommutative A) (hnorm : ∀ A ∈ S, U ≤ normalizer (A : Set X)) :
    sSup S ≤ puigLambda U :=
  sSup_le fun A hA => le_puigLambda (hab A hA) (hnorm A hA)

theorem le_puigLambda_of_le_iSup {U T : Subgroup X} {ι : Sort*} {A : ι → Subgroup X}
    (hT : T ≤ ⨆ i, A i) (hab : ∀ i, IsMulCommutative (A i))
    (hnorm : ∀ i, U ≤ normalizer (A i : Set X)) : T ≤ puigLambda U :=
  hT.trans (iSup_le_puigLambda hab hnorm)

theorem closure_iUnion_le_puigLambda {U : Subgroup X} {ι : Sort*} {A : ι → Subgroup X}
    (hab : ∀ i, IsMulCommutative (A i)) (hnorm : ∀ i, U ≤ normalizer (A i : Set X)) :
    closure (⋃ i, (A i : Set X)) ≤ puigLambda U := by
  rw [← iSup_eq_closure]
  exact iSup_le_puigLambda hab hnorm

end CFSG.FeitThompson

end
