module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41UA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem z18_V1_le_M (h : L41GPh15 t L S x₁ x₂ lam rho) :
    l41V1 t x₁ x₂ rho lam ≤ l41M t x₁ x₂ rho := by
  refine sup_le h.q1facts.normal_Q1.1 ?_
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.le_normalizer (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  · have hM := h.qfacts.M_eq
    rw [hM]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem z18_exists_V2 (h : L41GPh15 t L S x₁ x₂ lam rho) :
    ∃ V₂ : Subgroup G, IsPGroup 2 V₂ ∧ l41V1 t x₁ x₂ rho lam ≤ V₂ ∧
      V₂ ≤ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) ∧ ¬ 2 ∣ V₂.index := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) :=
    ⟨_, rfl⟩
  have hMH : l41M t x₁ x₂ rho ≤ H := by
    intro m hm
    rw [hH]
    exact mem_normalizer_of_conj_mem (fun y hy => h.mbasic.normal_Y.2 m hm y hy)
  have hV1H : l41V1 t x₁ x₂ rho lam ≤ H := (z18_V1_le_M h).trans hMH
  have hQ' : IsPGroup 2 ((l41V1 t x₁ x₂ rho lam).subgroupOf H) :=
    h.q1facts.V1_pGroup.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  refine ⟨(R : Subgroup ↥H).map H.subtype, ?_, ?_, ?_, ?_⟩
  · exact IsPGroup.of_surjective R.isPGroup' (H.subtype.subgroupMap (R : Subgroup ↥H))
      (MonoidHom.subgroupMap_surjective _ _)
  · intro v hv
    exact ⟨⟨v, hV1H hv⟩, hR (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  · rw [← hH]
    exact Subgroup.map_subtype_le _
  · have hodd : ¬ 2 ∣ H.index := by
      rw [hH]
      exact h.uniqueY.2
    have hRi : ¬ 2 ∣ (R : Subgroup ↥H).index := R.not_dvd_index
    rw [Subgroup.index_map_subtype]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h1 | h1
    · exact hRi h1
    · exact hodd h1

theorem z18_tG_Q1 (h : L41GPh16 t L S x₁ x₂ lam rho) (g : G) {u : G}
    (hu : u ∈ l41Q1 t x₁ x₂ rho) : g⁻¹ * t * g ≠ u := by
  intro hgu
  have hu' : u ∈ l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [h.centQ1]
    exact hu
  obtain ⟨hY1, hY2⟩ := h.yfacts.Y_elem
  refine l41_no_e16_cent_conj h.toL41GPh1 hY1 hY2 g⁻¹ ?_
  intro y hy
  rw [inv_inv, hgu]
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu').2 y hy)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
