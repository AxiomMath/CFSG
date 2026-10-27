module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Model

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem symm_mem_commutator_of_mem {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {y : B} (h : y ∈ _root_.commutator B) : e.symm y ∈ _root_.commutator A := by
  have hmap : (_root_.commutator A).map e.toMonoidHom = _root_.commutator B := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hy : y ∈ (_root_.commutator A).map e.toMonoidHom := by rw [hmap]; exact h
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  have hz' : z = e.symm y := by
    have h' : e z = y := hzy
    rw [← e.symm_apply_apply z, h']
  exact hz' ▸ hz

theorem fourB_exists_reps {G : Type} [Group G] {K : Subgroup G} (hK : IsShapeZ2TimesSym 6 ↥K) :
    ∃ r : Fin 7 → G, ∀ t ∈ K, orderOf t = 2 → ∃ j, ConjIn K t (r j) := by
  obtain ⟨e⟩ := hK
  obtain ⟨m, hm⟩ := symModel_reps
  refine ⟨fun j => ((e.symm (m j) : ↥K) : G), ?_⟩
  intro t ht ht2
  let y : ↥K := ⟨t, ht⟩
  have hy : orderOf y = 2 := by
    change orderOf (⟨t, ht⟩ : ↥K) = 2
    rw [Subgroup.orderOf_mk, ht2]
  have hey : orderOf (e y) = 2 := by rw [MulEquiv.orderOf_eq, hy]
  obtain ⟨j, hj⟩ := hm (e y) hey
  have hj' : IsConj y (e.symm (m j)) := by
    simpa using MonoidHom.map_isConj e.symm.toMonoidHom hj
  obtain ⟨k, hk⟩ := isConj_iff.mp hj'
  refine ⟨j, ?_⟩
  refine ⟨k, k.2, ?_⟩
  have hk' := congrArg (fun w : ↥K => (w : G)) hk
  simpa [y] using hk'

theorem fourB_exists_derived_involution {G : Type} [Group G] {K : Subgroup G}
    (hK : IsShapeZ2TimesSym 6 ↥K) : ∃ t ∈ derivedOf K, orderOf t = 2 := by
  obtain ⟨e⟩ := hK
  obtain ⟨u, hu, hu2⟩ := symModel_exists_derived_involution
  refine ⟨((e.symm u : ↥K) : G), ?_, ?_⟩
  · rw [mem_derivedOf_iff]
    exact ⟨(e.symm u).2, symm_mem_commutator_of_mem e hu⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hu2]

end CFSG.EvenSporadicStandard.HNRecog.Section3
